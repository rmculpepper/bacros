#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/set
         syntax/id-table
         syntax/parse
         "../analysis/util.rkt"
         "../analysis/expkind.rkt"
         "../analysis/binding.rkt")
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

(time (modfix (lambda () (analyze-expkind t-estx))))
(time (modfix (lambda () (analyze-binding t-estx))))

(printf "\nVAREXP expressions:\n")
(dump-tag-function VAREXP)

(printf "\nLAMBDAEXP expressions:\n")
(dump-tag-function LAMBDAEXP)

(printf "\nBINDING variables:\n")
(dump-var-function BINDING)
