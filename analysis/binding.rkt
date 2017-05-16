#lang racket/base
(require (rename-in racket/match [match-define defmatch])
         racket/set
         syntax/id-table
         syntax/parse
         syntax/stx
         "util.rkt")
(provide (all-defined-out))

;; BINDING : (GSTable Identifier Binding)
;; Connects identifiers to the expressions they are bound to.

;; Binding =
;; | #f               -- unknown (eg define-values w/o values rhs)
;; | (list Tag ...)   -- all tags from initial binding, set! rhss

;; b-join : Binding Binding -> Binding
(define (b-join b1 b2)
  (and b1 b2
       (for/fold ([b2 b2]) ([t (in-list b1)] #:unless (member t b2))
         (cons t b2))))

(define BINDING (make-var-get/set null b-join))

;; ----------------------------------------

;; RESULTEXP : (GSTable Tag Result)
;; Connects expr to result value(s) exprs.
;; eg, (values E1 E2) mapped to (list E1 E2)
;; eg, (let BS E)) mapped to result of E

;; Result = (Listof Tag/#f)

(define RESULTEXP (make-tag-get/set #f))

;; RESULTEXP-post : Syntax -> Void
(define (RESULTEXP-post stx)
  (syntax-parse stx
    #:literal-sets (kernel-literals) #:literals (values)
    [(begin e ... e*)
     (RESULTEXP stx (RESULTEXP #'e*))]
    [(begin0 e0 e ...)
     (RESULTEXP stx (RESULTEXP #'e0))]
    [(let-values BS body ... body*)
     (RESULTEXP stx (RESULTEXP #'body*))]
    [(letrec-values BS body ... body*)
     (RESULTEXP stx (RESULTEXP #'body*))]
    [(letrec-syntaxes+values SBS VBS body ... body*)
     (RESULTEXP stx (RESULTEXP #'body*))]
    [(#%plain-app values e ...)
     (RESULTEXP stx (map RESULTEXP1 (syntax->list #'(e ...))))]
    [_
     (RESULTEXP stx (list (tag stx)))]))

(define (RESULTEXP1 stx) (match (RESULTEXP stx) [(list t) t] [_ #f]))

;; ----------------------------------------

;; BINDING-pre : Syntax -> Void
(define (BINDING-pre stx)
  (define (multi vars vals)
    (if (= (length (stx->list vars)) (length vals))
        (for ([var (stx->list vars)] [val vals]) (BINDING var (list val)))
        (for ([var (stx->list vars)]) (BINDING var #f))))
  (syntax-parse stx
    #:literal-sets (kernel-literals)
    [(define-values (var:id ...) e)
     (multi #'(var ...) (RESULTEXP #'e))]
    [(let-values ([(var:id ...) rhs] ...) body ...)
     (for ([vars (in-list (syntax->list #'((var ...) ...)))]
           [rhs (in-list (syntax->list #'(rhs ...)))])
       (multi vars (RESULTEXP rhs)))]
    [(letrec-values ([(var:id ...) rhs] ...) body ...)
     (for ([vars (in-list (syntax->list #'((var ...) ...)))]
           [rhs (in-list (syntax->list #'(rhs ...)))])
       (multi vars (RESULTEXP rhs)))]
    [(letrec-syntaxes+values _sbinds ([(vvar:id ...) vrhs] ...) body ...)
     (for ([vars (in-list (syntax->list #'((vvar ...) ...)))]
           [rhs (in-list (syntax->list #'(vrhs ...)))])
       (multi vars (RESULTEXP rhs)))]
    [(set! var e)
     (let ([r (RESULTEXP1 #'e)])
       (BINDING #'var (and r (list r))))]
    [_ (void)]))

;; ----------------------------------------

(define (analyze-binding stx)
  (traverse stx void RESULTEXP-post)
  (traverse stx BINDING-pre void))
