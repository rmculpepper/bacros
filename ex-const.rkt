#lang racket/base
(require racket/match
         syntax/id-table
         syntax/parse
         "lib.rkt")
(provide (all-defined-out))

;; A ConstInfo (CI) is one of
;; - 'top           -- no known values
;; - (datum Datum)  -- exactly one known value (a flat datum)
;; - (lam (Listof Id) Tag) -- exactly one known value (a lambda)
;; - 'bot           -- more than one possible value or value is not datum
(struct datum (value) #:transparent)
(struct lam (args result) #:transparent)

;; ci-join : CI CI -> CI
(define (ci-join c1 c2)
  (cond [(equal? c1 c2) c1]
        [(eq? c1 'top) c2]
        [(eq? c2 'top) c1]
        [else 'bot]))

;; ci-contains-truth : CI -> Boolean
(define (ci-contains-truth c)
  (match c
    ['bot #t]
    ['top #f]
    [(datum v) (and v #t)]
    [(lam _ _) #t]))

;; ci-contains : CI Datum -> Boolean
(define (ci-contains c d)
  (match c
    ['bot #t]
    ['top #f]
    [(datum v) (equal? v d)]
    [(lam _ _) #f]))

;; lift-apply : Procedure (Listof CI) -> CI
(define (lift-apply f cs)
  (cond [(for/or ([c cs]) (eq? c 'top))
         (eprintf "suspicious: top inside of application... ~s to ~s\n" f cs)]
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
(add-folding-prims + - * / zero? = > < <= >=)

(define-syntax-class folding-prim
  #:attributes (proc)
  #:opaque
  (pattern f:id
           #:attr proc (free-id-table-ref folding-prims-table #'f #f)
           #:when (attribute proc)))

;; ============================================================

(define e-const (make-tag-get/set 'top ci-join))
(define v-const (make-var-get/set 'top ci-join))

(define (vs-const vs info)
  (syntax-parse vs
    [(var) (v-const #'var info)]
    [(var ...) (for ([var (syntax->list #'(var ...))]) (v-const #'var 'bot))]))

(define (es-const es)
  (map e-const (syntax->list es)))

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
    [(define-syntaxes . _) stx]
    [(#%require . _) stx]
    ;; -- expr
    [var:id
     (e-const stx (v-const #'var))]
    [(#%plain-lambda (var ...) e ...)
     (vs-const #'(var ...) 'bot)
     (analyze* #'(e ...))
     (e-const stx 'bot)]
    [(case-lambda [(var ...) e ...] ...)
     (vs-const #'(var ... ...) 'bot)
     (analyze #'(e ... ...))
     (e-const stx 'bot)]
    [(if e1 e2 e3)
     (analyze #'e1)
     (when (ci-contains-truth (e-const #'e1))
       (analyze #'e2)
       (e-const stx (e-const #'e2)))
     (when (ci-contains (e-const #'e1) #f)
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
    [(letrec-values ([vars rhs] ...) body ...)
     (modfix
      (lambda ()
        (for ([vars (syntax->list #'(vars ...))]
              [e (syntax->list #'(rhs ...))])
          (analyze e)
          (vs-const vars (e-const e)))
        (analyze* #'(body ... body*))))
     (e-const stx (e-const #'body*))]
    [(letrec-syntaxes+values ([svars srhs] ...) ([vvars vrhs] ...) body ...)
     (modfix
      (lambda ()
        (for ([vvars (syntax->list #'(vvars ...))]
              [e (syntax->list #'(vrhs ...))])
          (analyze e)
          (vs-const vvars (e-const e)))
        (analyze* #'(body ... body*))))
     (e-const stx (e-const #'body*))]
    [(set! var e)
     (v-const #'var 'bot)
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
    [(#%plain-app e ...)
     (analyze* #'(e ...))
     (e-const stx 'bot)]
    [_
     (raise-syntax-error #f "unhandled syntax" stx)]
    ))

(define (analyze* stx)
  (for ([stx (syntax->list stx)])
    (analyze stx)))

(module+ demo
  (define stx
    #'(begin (define a 1) (define b 2) (define c (+ a b)) (define d 5)
             (define (f x)
               (when (> c b)
                 (set! d x))
               (when (> a b) ;; never
                 (set! a (sub1 a))) ;; shouldn't infect a
               (* c x))))
  (define estx (expand stx))
  (define t-estx (add-tags estx))
  ;; (analyze t-estx)
  (modfix (lambda () (analyze t-estx)))
  (printf "Expressions:\n")
  (dump-tag-function e-const)
  (printf "\nVariables:\n")
  (dump-var-function v-const))
