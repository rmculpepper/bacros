#lang racket/base
(require (for-syntax racket/base
                     syntax/id-table
                     syntax/parse
                     syntax/parse/experimental/template
                     "tag.rkt"))
(provide declare-analysis
         define-special-function
         (for-syntax (all-from-out "tag.rkt")))

(begin-for-syntax
  (define analysis-hooks (box null)))

(define-syntax (declare-analysis stx)
  (syntax-parse stx
    [(_ rhs:expr)
     #'(begin-for-syntax
         (let ([analysis rhs])
           (set-box! analysis-hooks (cons analysis (unbox analysis-hooks)))))]))

;; invalidate-analysis : -> Void
;; TODO: Invalidates analysis (called by special-function transformers).

;; ============================================================

;; define-special-function
;; (define-special-function id transformer)
;; Called after expansion, after analysis.
;; If invalidates analysis, must call invalidate-analysis.

;; ============================================================

(begin-for-syntax
  ;; special-functions : id-table[ Syntax -> Syntax ]
  (define special-functions (make-free-id-table))

  (define-syntax-class special-function
    #:attributes (transformer)
    (pattern x:id
             #:attr transformer (free-id-table-ref special-functions #'x #f)
             #:when (attribute transformer)))
  )

(define-syntax (define-special-function stx)
  (syntax-parse stx
    [(_ name:id rhs:expr)
     #'(begin (define name special-function-value)
              (begin-for-syntax
                (free-id-table-set! (quote-syntax name) rhs)))]
    [(_ (name:id . args) rhs:expr)
     #'(define-special-function name (lambda args rhs))]))

;; ============================================================

(define-syntax (special-module-begin stx)
  (syntax-case stx ()
    [(_ form ...)
     (let ()
       (define e-body
         (local-expand #'(#%plain-module-begin form ...)
                       (syntax-local-context)
                       null))
       (add-tags e-body)
       (for ([analyze (in-list (reverse (analysis-hooks)))])
         (analyze e-body))
       (with-syntax ([(_ tx-form ...) (transform e-body)])
         #'(#%module-begin tx-form ...)))]))

;; ============================================================

(begin-for-syntax

  ;; Need privileged inspector to rewrite expanded code.
  (define stx-insp
    (variable-reference->module-declaration-inspector
     (#%variable-reference)))

  ;; transform : Syntax -> Syntax
  ;; Traverse the expanded code, rewriting occurrences of special
  ;; functions. We don't rewrite the rewritten forms of special
  ;; functions, though. (Need to expand, maybe analyze, again before
  ;; we can do that.)
  (define (transform stx0)
    (define-template-metafunction recur
      (syntax-parser [(recur e) (transform #'e)]))
    (define-syntax-rule (T tmpl)
      (relocate (template tmpl) stx0))
    (define stx (syntax-disarm stx0 stx-insp))
    (define processed-stx
      (syntax-parse stx
        #:literal-sets (kernel-literals)
        ;; Fully-Expanded Programs
        ;; -- module body
        [(#%plain-module-begin form ...)
         (T (#%plain-module-begin (recur form) ...))]
        ;; -- module-level form
        [(#%provide . _) stx]
        [(begin-for-syntax . _) stx]
        [(module . _) stx]
        [(module* . _) stx]
        [(#%declare . _) stx]
        ;; -- general top-level form
        [(define-values ids e)
         (T (define-values ids (recur e)))]
        [(define-syntaxes . _) stx]
        [(#%require . _) stx]
        ;; -- expr
        [var:id #'var]
        [(#%plain-lambda formals e ...)
         (T (#%plain-lambda formals (recur e) ...))]
        [(case-lambda [formals e ...] ...)
         (T (case-lambda [formals (recur e) ...] ...))]
        [(if e1 e2 e3)
         (T (if (recur e1) (recur e2) (recur e3)))]
        [(begin e ...)
         (T (begin (recur e) ...))]
        [(begin0 e ...)
         (T (begin0 (recur e) ...))]
        [(let-values ([vars rhs] ...) body ...)
         (T (let-values ([vars (recur rhs)] ...)
              (recur body) ...))]
        [(letrec-values ([vars rhs] ...) body ...)
         (T (letrec-values ([vars (recur rhs)] ...)
                           (recur body) ...))]
        [(letrec-syntaxes+values ([svars srhs] ...) ([vvars vrhs] ...) body ...)
         (T (letrec-syntaxes+values ([svars srhs] ...) ([vvars (recur vrhs)] ...)
                                    (recur body) ...))]
        [(set! var e)
         (T (set! var (recur e)))]
        [(quote d) stx]
        [(quote-syntax . _) stx]
        [(with-continuation-mark e1 e2 e3)
         (T (with-continuation-mark (recur e1) (recur e2) (recur e3)))]
        [(#%top . _) stx]
        [(#%variable-reference . _) stx]
        [(#%expression e)
         (T (#%expression (recur e)))]
        ;; -- application
        [(#%plain-app f:special-function e ...)
         (with-syntax ([(e* ...) (template ((recur e) ...))])
           (apply-transformer (attribute f.transformer) (T (f e* ...)) #'f))]
        [(#%plain-app e ...)
         (T (#%plain-app (recur e) ...))]
        [_
         (raise-syntax-error #f "unhandled syntax" stx)]
        ))
    ;; Rearm and track result
    (syntax-rearm
     (syntax-property processed-stx 'original-for-check-syntax #t)
     stx0))

  (define current-special-function-introducer (make-parameter values))

  (define (apply-transformer f stx f-stx)
    (define mark (make-syntax-introducer))
    (define tx-stx
      (parameterize ((current-special-function-introducer mark))
        (mark (f (mark stx)))))
    (syntax-track-origin tx-stx stx f-stx))

  (define (relocate stx loc-stx)
    (datum->syntax stx (syntax-e stx) loc-stx loc-stx))

  )

;; ============================================================

(module reader syntax/module-reader
  bacros)

;; ============================================================

;; The Macro Conjecture: Any (reasonable) macro can be divided into a
;; syntax transformer that depends only on the binding structure of
;; the macro plus a function that implements the macro's dynamic
;; behavior.

;; The Bacro Strategy: If the latter function is a special function,
;; can do type-specific "expansion".
