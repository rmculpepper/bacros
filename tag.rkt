#lang racket/base
(require syntax/parse
         syntax/stx
         syntax/parse/experimental/template)
(provide tag
         new-tag
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
      [(S:#%plain-module-begin form ...)
       (T (S (recur form) ...))]
      ;; -- module-level form
      [(#%provide . _) stx]
      [(begin-for-syntax . _) stx]
      [(module . _) stx]
      [(module* . _) stx]
      [(#%declare . _) stx]
      ;; -- general top-level form
      [(S:define-values ids e)
       (T (S ids (recur e)))]
      [(define-syntaxes . _) stx]
      [(#%require . _) stx]
      ;; -- expr
      [var:id #'var]
      [(S:#%plain-lambda formals e ...)
       (T (S formals (recur e) ...))]
      [(S:case-lambda [formals e ...] ...)
       (T (S [formals (recur e) ...] ...))]
      [(S:if e1 e2 e3)
       (T (S (recur e1) (recur e2) (recur e3)))]
      [(S:begin e ...)
       (T (S (recur e) ...))]
      [(S:begin0 e ...)
       (T (S (recur e) ...))]
      [(S:let-values ([vars rhs] ...) body ...)
       (T (S ([vars (recur rhs)] ...)
            (recur body) ...))]
      [(S:letrec-values ([vars rhs] ...) body ...)
       (T (S ([vars (recur rhs)] ...)
            (recur body) ...))]
      [(S:letrec-syntaxes+values ([svars srhs] ...) ([vvars vrhs] ...) body ...)
       (T (S ([svars srhs] ...) ([vvars (recur vrhs)] ...)
            (recur body) ...))]
      [(S:set! var e)
       (T (S var (recur e)))]
      [(quote d) stx]
      [(quote-syntax . _) stx]
      [(S:with-continuation-mark e1 e2 e3)
       (T (S (recur e1) (recur e2) (recur e3)))]
      [(S:#%plain-app f:id e ...)
       (T (S (recur f) (recur e) ...))]
      [(S:#%plain-app f e ...)
       (with-syntax ([(ftmp) (generate-temporaries #'(f))])
         (T (recur (let-values ([(ftmp) f]) (S ftmp e ...)))))]
      [(#%top . _) stx]
      [(#%variable-reference . _) stx]
      [(S:#%expression e)
       (T (S (recur e)))]
      [_
       (raise-syntax-error 'add-tags "unhandled syntax" stx)]
      ))
  ;; Rearm and track result
  (syntax-rearm
   (syntax-property
    (syntax-property processed-stx 'tag the-tag)
    'original-for-check-syntax #t)
   stx0))

(define (relocate stx loc-stx)
  (datum->syntax loc-stx (syntax-e stx) loc-stx loc-stx))

(define (syntax-summary stx)
  (if (syntax? stx)
      (format "~a:~a ~.s"
              (or (syntax-line stx) "?")
              (or (syntax-column stx) "?")
              (syntax->datum stx))
      (format "~a" stx)))
