#lang racket/base
(require racket/base
         racket/dict
         (rename-in racket/match [match-define defmatch])
         syntax/id-table
         syntax/parse
         syntax/parse/experimental/template
         "tag.rkt")
(provide (all-from-out "tag.rkt")
         (all-defined-out))

;; mods : Nat
;; Global counter for modifications.
(define mods 0)

;; modfix : (-> Void) -> Void
;; Runs given function until no more modifications.
(define (modfix proc)
  (let ([old-mods mods])
    (proc)
    (unless (= mods old-mods)
      (eprintf "** new mods, going again\n")
      (modfix proc))))

(struct gs (dict top join get-key)
        #:property prop:procedure
        (case-lambda
          [(self k)
           (defmatch (gs dict top join get-key) self)
           (dict-ref dict (get-key k) top)]
          [(self k v)
           (defmatch (gs dict top join get-key) self)
           (let* ([old (dict-ref dict (get-key k) top)]
                  [new (join old v)])
             (unless (equal? new old)
               (set! mods (add1 mods)))
             (dict-set! dict (get-key k) new))]))

;; make-get/set : Dict[K=>V] V (V V -> V) #:key (K* -> K)
;;             -> (case-> (K* -> V) (K* V -> Void))
(define (make-get/set dict top join #:key [get-key values])
  (gs dict top join get-key))

(define (make-tag-get/set top join)
  (make-get/set (make-hash) top join #:key (lambda (x) (if (syntax? x) (tag x) x))))

(define (make-var-get/set top join)
  (make-get/set (make-free-id-table) top join #:key values))

(define (dump-tag-function self)
  (defmatch (gs dict top join get-key) self)
  (define keys (sort (dict-keys dict) <))
  (for ([k (in-list keys)])
    (printf "~s => ~v  -- ~a\n" k (dict-ref dict k) (tag-summary k))))

(define (dump-var-function self)
  (defmatch (gs dict top join get-key) self)
  (for ([(k v) (in-dict dict)])
    (printf "~s => ~v\n" k v)))
