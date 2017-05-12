#lang racket/base
(require (for-syntax racket/base syntax/parse)
         "main.rkt")
(provide (all-defined-out))

;; No analysis

;; Declare special functions
(begin-for-syntax
  (define ((make-folding op) stx)
    (syntax-parse stx
      #:literals (quote)
      [(_ (quote arg) ...)
       (with-syntax ([result (apply op (syntax->datum #'(arg ...)))])
         #'(quote result))]
      [_ stx])))

(declare-special-function + (make-folding +))
(declare-special-function * (make-folding *))
(declare-special-function - (make-folding -))

(syntax->datum
 (expand
  #'(special-begin
     (lambda (x)
       (+ (* 2 (+ 1 4)) (* 2 x) 4)))))
