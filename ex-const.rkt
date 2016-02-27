#lang racket/base
(require racket/match
         syntax/id-table
         syntax/parse
         "lib.rkt")
(provide (all-defined-out))

;; A ConstInfo is one of
;; - 'top           -- no known values
;; - (const Datum)  -- exactly one known value
;; - 'bot           -- more than one possible value or value is not datum
(struct const (datum) #:transparent)

;; constinfo-join : ConstInfo ConstInfo -> ConstInfo
(define (constinfo-join c1 c2)
  (cond [(eq? c1 'top) c2]
        [(eq? c2 'top) c1]
        [(eq? c1 'bot) 'bot]
        [(eq? c2 'bot) 'bot]
        [(equal? (const-datum c1) (const-datum c2)) c1]
        [else 'bot]))

(define (constinfo-contains-truth c)
  (match c
    ['bot #t]
    ['top #f]
    [(const v) (and v #t)]))

(define (constinfo-contains c v)
  (match c
    ['bot #t]
    ['top #f]
    [(const datum) (equal? v datum)]))

(define (lift-apply f cs)
  (cond [(for/or ([c cs]) (eq? c 'top))
         (eprintf "suspicious: top inside of application... ~s to ~s\n" f cs)]
        [(for/or ([c cs]) (eq? c 'bot)) 'bot]
        [else
         (with-handlers ([(lambda (e) #t)
                          (lambda (e)
                            (eprintf "lift-apply: got exn ~s\n" (exn-message e))
                            'bot)])
           (const (apply f (map const-datum cs))))]))

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

(define e-const (make-tag-get/set 'top constinfo-join))
(define v-const (make-var-get/set 'top constinfo-join))

(define (vs-const vs info)
  (syntax-parse vs
    [(var) (v-const #'var info)]
    [(var ...) (for ([var (syntax->list #'(var ...))]) (v-const #'var 'bot))]))

(define (es-const es)
  (map e-const (syntax->list es)))

(define (analyze-const stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    ;; Fully-Expanded Programs
    ;; -- module body
    [(#%plain-module-begin form ...)
     (modfix (lambda () (analyze-const* #'(form ...))))]
    ;; -- module-level form
    [(#%provide . _) (void)]
    [(begin-for-syntax . _) (void)]
    [(module . _) (void)]
    [(module* . _) (void)]
    [(#%declare . _) (void)]
    ;; -- general top-level form
    [(define-values vars e)
     (analyze-const #'e)
     (vs-const #'vars (e-const #'e))]
    [(define-syntaxes . _) stx]
    [(#%require . _) stx]
    ;; -- expr
    [var:id
     (e-const stx (v-const #'var))]
    [(#%plain-lambda (var ...) e ...)
     (vs-const #'(var ...) 'bot)
     (analyze-const* #'(e ...))
     (e-const stx 'bot)]
    [(case-lambda [(var ...) e ...] ...)
     (vs-const #'(var ... ...) 'bot)
     (analyze-const #'(e ... ...))
     (e-const stx 'bot)]
    [(if e1 e2 e3)
     (analyze-const #'e1)
     (when (constinfo-contains-truth (e-const #'e1))
       (analyze-const #'e2)
       (e-const stx (e-const #'e2)))
     (when (constinfo-contains (e-const #'e1) #f)
       (analyze-const #'e3)
       (e-const stx (e-const #'e3)))]
    [(begin e ... e*)
     (analyze-const* #'(e ... e*))
     (e-const stx (e-const #'e*))]
    [(begin0 e* e ...)
     (analyze-const* #'(e* e ...))
     (e-const stx (e-const #'e*))]
    [(let-values ([vars rhs] ...) body ... body*)
     (for ([vars (syntax->list #'(vars ...))]
           [e (syntax->list #'(rhs ...))])
       (analyze-const e)
       (vs-const vars (e-const e)))
     (analyze-const* #'(body ... body*))
     (e-const stx (e-const #'body*))]
    [(letrec-values ([vars rhs] ...) body ...)
     (modfix
      (lambda ()
        (for ([vars (syntax->list #'(vars ...))]
              [e (syntax->list #'(rhs ...))])
          (analyze-const e)
          (vs-const vars (e-const e)))
        (analyze-const* #'(body ... body*))))
     (e-const stx (e-const #'body*))]
    [(letrec-syntaxes+values ([svars srhs] ...) ([vvars vrhs] ...) body ...)
     (modfix
      (lambda ()
        (for ([vvars (syntax->list #'(vvars ...))]
              [e (syntax->list #'(vrhs ...))])
          (analyze-const e)
          (vs-const vvars (e-const e)))
        (analyze-const* #'(body ... body*))))
     (e-const stx (e-const #'body*))]
    [(set! var e)
     (v-const #'var 'bot)
     (e-const stx (const (void)))]
    [(quote d)
     (e-const stx (const (syntax->datum #'d)))]
    [(quote-syntax . _)
     (e-const stx 'bot)]
    [(with-continuation-mark e1 e2 e3)
     (analyze-const* #'(e1 e2 e3))
     (e-const stx (e-const #'e3))]
    [(#%top . var:id)
     (e-const stx (v-const #'var))]
    [(#%variable-reference . _)
     (e-const stx 'bot)]
    [(#%expression e)
     (analyze-const #'e)
     (e-const stx (e-const #'e))]
    ;; -- application
    [(#%plain-app f:folding-prim e ...)
     (analyze-const* #'(e ...))
     (e-const stx (lift-apply (attribute f.proc) (es-const #'(e ...))))]
    [(#%plain-app e ...)
     (analyze-const* #'(e ...))
     (e-const stx 'bot)]
    [_
     (raise-syntax-error #f "unhandled syntax" stx)]
    ))

(define (analyze-const* stx)
  (for ([stx (syntax->list stx)])
    (analyze-const stx)))

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
  (analyze-const t-estx)
  ;; (modfix (lambda () (analyze-const t-estx)))
  (printf "Expressions:\n")
  (dump-tag-function e-const)
  (printf "\nVariables:\n")
  (dump-var-function v-const))
