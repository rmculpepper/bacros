#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/set
         syntax/id-table
         syntax/parse
         "../lib.rkt")
(provide (all-defined-out))

(define external-id (add-tags (datum->syntax #f 'EXTERNAL)))

;; An Info is one of
;; - top
;; - (datum Datum)
;; - 'bot
;; - (setof Lam)
;; - (cons 'bot (setof Lam))
(struct datum (value) #:transparent)

;; A Lam is one of (lam (Listof Id) Tag) or 'HAVOC
(struct lam (args result) #:transparent)

(define (info-datum-part i)
  (cond [(pair? i) (car i)]
        [(set? i) 'top]
        [else i]))
(define (info-lams-part i)
  (cond [(pair? i) (cdr i)]
        [(set? i) i]
        [else (set)]))
(define (make-info datum-part lams-part)
  (cond [(set-empty? lams-part) datum-part]
        [(eq? datum-part 'top) lams-part]
        [else (cons 'bot lams-part)]))

;; i-join : I I -> I
(define (i-join i1 i2)
  (make-info (ci-join (info-datum-part i1) (info-datum-part i2))
             (set-union (info-lams-part i1) (info-lams-part i2))))

;; i-join* : (Listof I) -> I
(define (i-join* is) (foldl i-join 'top is))

(define (i-contains-truth i b)
  (or (ci-contains-truth (info-datum-part i) b)
      (and b (not (set-empty? (info-lams-part i))))))

;; A ConstInfo (CI) is one of
;; - 'top           -- no known values
;; - (datum Datum)  -- exactly one known value (a flat datum)
;; - 'bot           -- more than one possible value or value is not datum

;; ci-join : CI CI -> CI
(define (ci-join c1 c2)
  (cond [(equal? c1 c2) c1]
        [(eq? c1 'top) c2]
        [(eq? c2 'top) c1]
        [else 'bot]))

;; ci-contains-truth : CI Boolean -> Boolean
;; #t means any true value, #f means #f
(define (ci-contains-truth c b)
  (match c
    ['bot #t]
    ['top #f]
    [(datum v) (equal? (and v #t) b)]))

;; lift-apply : Procedure (Listof I) -> I
;; Safe only for pure first-order procedures.
(define (lift-apply f cs)
  (cond [(for/or ([c cs]) (eq? c 'top))
         (eprintf "suspicious: top inside of application... ~s to ~s\n" f cs)
         'top]
        [(andmap datum? cs)
         (with-handlers ([(lambda (e) #t)
                          (lambda (e)
                            (eprintf "lift-apply: got exn ~s\n" (exn-message e))
                            'bot)])
           (datum (apply f (map datum-value cs))))]
        [else 'bot]))

(define folding-prims-table (make-free-id-table))
(define-syntax-rule (add-folding-prims id ...)
  (begin (free-id-table-set! folding-prims-table (quote-syntax id) id) ...))
(add-folding-prims + - * / zero? = > < <= >= void)

(define-syntax-class folding-prim
  #:attributes (proc)
  #:opaque
  (pattern f:id
           #:attr proc (free-id-table-ref folding-prims-table #'f #f)
           #:when (attribute proc)))

;; ============================================================

(define e-const (make-tag-get/set 'top i-join))
(define v-const (make-var-get/set 'top i-join))

(define (vs-const vs info)
  (syntax-parse vs
    [(var) (v-const #'var info)]
    [(var ...) (for ([var (syntax->list #'(var ...))]) (v-const #'var 'bot))]))

(define (es-const es)
  (map e-const (syntax->list es)))

(define ((seq . fs)) (for ([f (in-list fs)]) (f)))

;; analyze : Syntax -> Void
(define (analyze stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    ;; Fully-Expanded Programs
    ;; -- module body
    [(#%plain-module-begin form ...)
     (modfix (lambda () (analyze* #'(form ...))))]
    ;; -- module-level form
    [(#%provide . _) (void)]
    [(begin-for-syntax . _) (void)]
    [(module . _) (void)]
    [(module* . _) (void)]
    [(#%declare . _) (void)]
    ;; -- general top-level form
    [(define-values vars e)
     (analyze #'e)
     (vs-const #'vars (e-const #'e))]
    [(define-syntaxes . _) (void)]
    [(#%require . _) (void)]
    ;; -- expr
    [var:id
     (e-const stx (v-const #'var))]
    [(#%plain-lambda (var ...) e ... e*)
     (analyze* #'(e ... e*))
     (e-const stx (set (lam (syntax->list #'(var ...)) (tag #'e*))))]
    [(case-lambda [(var ...) e ... e*] ...)
     ;; Treat a case-lambda as many separate lambdas
     (analyze* #'(e ... ...))
     (e-const stx
              (for/set ([vars (syntax->list #'((var ...) ...))]
                        [e* (syntax->list #'(e* ...))])
                (lam (syntax->list vars) (tag e*))))]
    [(if e1 e2 e3)
     (analyze #'e1)
     (when (i-contains-truth (e-const #'e1) #t)
       (eprintf "-- analyzing true branch because ~v\n" (e-const #'e1))
       (analyze #'e2)
       (e-const stx (e-const #'e2)))
     (when (i-contains-truth (e-const #'e1) #f)
       (eprintf "-- analyzing false branch because ~v\n" (e-const #'e1))
       (analyze #'e3)
       (e-const stx (e-const #'e3)))]
    [(begin e ... e*)
     (analyze* #'(e ... e*))
     (e-const stx (e-const #'e*))]
    [(begin0 e* e ...)
     (analyze* #'(e* e ...))
     (e-const stx (e-const #'e*))]
    [(let-values ([vars rhs] ...) body ... body*)
     (for ([vars (syntax->list #'(vars ...))]
           [e (syntax->list #'(rhs ...))])
       (analyze e)
       (vs-const vars (e-const e)))
     (analyze* #'(body ... body*))
     (e-const stx (e-const #'body*))]
    [(letrec-values ([vars rhs] ...) body ... body*)
     (modfix
      (lambda ()
        (for ([vars (syntax->list #'(vars ...))]
              [e (syntax->list #'(rhs ...))])
          (analyze e)
          (vs-const vars (e-const e)))
        (analyze* #'(body ... body*))))
     (e-const stx (e-const #'body*))]
    [(letrec-syntaxes+values ([svars srhs] ...) ([vvars vrhs] ...) body ... body*)
     (modfix
      (lambda ()
        (for ([vvars (syntax->list #'(vvars ...))]
              [e (syntax->list #'(vrhs ...))])
          (analyze e)
          (vs-const vvars (e-const e)))
        (analyze* #'(body ... body*))))
     (e-const stx (e-const #'body*))]
    [(set! var e)
     (analyze #'e)
     (v-const #'var (e-const #'e))
     (e-const stx (datum (void)))]
    [(quote d)
     (e-const stx (datum (syntax->datum #'d)))]
    [(quote-syntax . _)
     (e-const stx 'bot)]
    [(with-continuation-mark e1 e2 e3)
     (analyze* #'(e1 e2 e3))
     (e-const stx (e-const #'e3))]
    [(#%top . var:id)
     (e-const stx (v-const #'var))]
    [(#%variable-reference . _)
     (e-const stx 'bot)]
    [(#%expression e)
     (analyze #'e)
     (e-const stx (e-const #'e))]
    ;; -- application
    [(#%plain-app f:folding-prim e ...)
     (analyze* #'(e ...))
     (e-const stx (lift-apply (attribute f.proc) (es-const #'(e ...))))]
    [(#%plain-app f e ...)
     (analyze* #'(f e ...))
     (e-const stx (analyze-apply #'f (syntax->list #'(e ...))))]
    [_
     (raise-syntax-error #f "unhandled syntax" stx)]
    ))

(define (analyze* stx)
  (for ([stx (syntax->list stx)])
    (analyze stx)))

(define (analyze-apply f es)
  (i-join*
   (cons
    (match (info-datum-part (e-const f))
      ['top 'top]
      [(datum _) #| apply fails |# 'top]
      ['bot #| could be unknown procedure |# 'bot])
    (for/list ([l (in-set (info-lams-part (e-const f)))])
      (match l
        [(lam args result)
         (cond [(= (length args) (length es))
                (for ([arg args] [e es])
                  (v-const arg (e-const e)))
                (e-const result)]
               [else #| apply fails |# 'top])]
        ['HAVOC
         (wreak-havoc es)
         (v-const external-id)])))))

(define (wreak-havoc es)
  (for ([e es]) (v-const external-id (e-const e)))
  (for ([l (in-set (info-lams-part (v-const external-id)))])
    (match l
      [(lam args result)
       (for ([arg args]) (v-const arg (v-const external-id)))
       ;;(wreak-havoc result)
       (v-const external-id (e-const result))]
      ['HAVOC (void)]))
  (e-const external-id (v-const external-id)))

;; external-id starts at 'bot (so we don't need to add it later)
(v-const external-id (cons 'bot (set 'HAVOC)))

;; ============================================================

(module+ main
  (provide (all-defined-out))
  (define stx
    #'(begin (define a 1)
             (define b 2)
             (define c (+ a b))
             (define d 5)
             (define (ka _p) a)
             (define (kka _q) ka)
             (define (f x)
               (when (> ((kka 12) 7) b) ;; never
                 (set! a (sub1 a))) ;; shouldn't infect a
               (* c x))
             f))
  (define estx (expand stx))
  (define t-estx (add-tags estx))
  (time (modfix (lambda () (analyze t-estx) (wreak-havoc (list t-estx)))))
  (printf "Expressions:\n")
  (dump-tag-function e-const)
  (printf "\nVariables:\n")
  (dump-var-function v-const))
