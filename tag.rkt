#lang racket/base
(require syntax/parse
         syntax/parse/experimental/template)
(provide tag
         add-tags
         tag-table
         tag-summary)

;; Tagging: add integer label for each form

(define tag-counter 0)

;; tag-table : hash[Tag => Syntax]
(define tag-table (make-hash))

;; new-tag : Syntax -> Tag
(define (new-tag stx)
  (set! tag-counter (add1 tag-counter))
  (hash-set! tag-table tag-counter stx)
  tag-counter)

;; tag : Syntax -> Tag
(define (tag stx)
  (or (syntax-property stx 'tag)
      (error 'tag "no tag for: ~a\n" (syntax-summary stx))))

;; tag-summary : Tag -> String
(define (tag-summary tagn)
  (syntax-summary (hash-ref tag-table tagn)))

;; Need privileged inspector to rewrite expanded code.
(define stx-insp
  (variable-reference->module-declaration-inspector
   (#%variable-reference)))

;; add-tags : Syntax -> Syntax
;; Add unique tags to all forms under 'tag syntax-property.
;; Also introduce names for all expressions in operator position.
(define (add-tags stx0)
  (define-template-metafunction recur
    (syntax-parser [(recur e) (add-tags #'e)]))
  (define-syntax-rule (T tmpl)
    (relocate (template tmpl) stx0))
  (define stx (syntax-disarm stx0 stx-insp))
  (define the-tag (new-tag stx))
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
      [(#%plain-app f:id e ...)
       (T (#%plain-app (recur f) (recur e) ...))]
      [(#%plain-app f e ...)
       (with-syntax ([(ftmp) (generate-temporaries #'(f))])
         (T (recur (let-values ([(ftmp) f]) (#%plain-app ftmp e ...)))))]
      [(#%top . _) stx]
      [(#%variable-reference . _) stx]
      [(#%expression e)
       (T (#%expression (recur e)))]
      [_
       (raise-syntax-error #f "unhandled syntax" stx)]
      ))
  ;; Rearm and track result
  (syntax-rearm
   (syntax-property
    (syntax-property processed-stx 'tag the-tag)
    'original-for-check-syntax #t)
   stx0))

(define (relocate stx loc-stx)
  (datum->syntax stx (syntax-e stx) loc-stx loc-stx))

(define (syntax-summary stx)
  (format "~a:~a ~.s"
          (or (syntax-line stx) "?")
          (or (syntax-column stx) "?")
          (syntax->datum stx)))
