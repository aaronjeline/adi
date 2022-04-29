#lang racket
(provide list-ref/set exp? variable? label-exp? label? define/pred prim? label-prim? label-variable? ∪ zip)


(define-syntax (define/pred stx)
  (syntax-case stx ()
    [(_ name body)   
     #`(begin
         (define (name e)
           (match e
             [body #t]
             [_ #f])))]))

;; zips two lists together
(define (zip a b)
  (map list a b))

;; set union but allows empty arguments
(define (∪ . xs)
  (if (empty? xs)
      (set)
      (apply set-union xs)))

;;list-ref but returns but returns empty set if not found
(define/contract (list-ref/set lst i)
  (-> (listof set?) exact-nonnegative-integer? set?)
  (with-handlers
      [(exn:fail:contract?
        (λ (e) (set)))]
    (list-ref lst i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; predicates
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; predicates for different kinds of expressions, useful for contracts

(define (exp? e)
  ((or/c
    prim?
    variable?
    if?
    let?
    λ?
    rec?
    begin?
    pledge?
    syscall?
    (listof exp?)) e))
;; need to add
;; apply lamrest lamcase

(define (prim? e)
  (match e
    [(? number?) #t]
    [(? boolean?) #t]
    [(? empty-symb?) #t]
    [(? char?) #t]
    [(? string?) #t]
    [_ #f]))

(define (variable? x)
  (and (symbol? x)
       (not (equal? x 'empty))))

(define/pred label? (list 'label (? symbol?)))
(define/pred if? (list 'if (? exp?) (? exp?) (? exp?)))
(define/pred let? (list 'let (list (list (? symbol?) (? exp?))) (? exp?)))
(define/pred λ? (list 'λ (? (listof symbol?)) (? exp?)))
(define/pred rec? (list 'rec (? symbol?) (? (listof symbol?)) (? exp?)))
(define/pred begin? (cons 'begin (? (listof exp?))))
(define/pred syscall? (cons 'syscall (cons (? symbol?) (? (listof exp?)))))
(define/pred pledge? (list 'pledge (? symbol?)))

(define (label-exp? e)
  ((or/c
    label-prim?
    label-variable?
    label-if?
    label-let?
    label-λ?
    label-rec?
    label-begin?
    label-syscall?
    pledge?
    (list/c app? label? (listof exp?))) e))

(define/pred label-prim? (list 'prim (? label?) (? prim?)))
(define (app? e)
  (equal? e 'app))
(define (empty-symb? s)
  (equal? s 'empty))

(define/pred label-if? (list 'if (? label?) (? label-exp?) (? label-exp?) (? label-exp?)))
(define/pred label-let? (list 'let (? label?) (list (list (? symbol?) (? label-exp?))) (? label-exp?)))
(define/pred label-λ? (list 'λ (? label?) (? (listof symbol?)) (? label-exp?)))
(define/pred label-rec? (list 'rec (? label?) (? symbol?) (? (listof symbol?)) (? label-exp?)))
(define/pred label-begin? (cons 'begin (cons (? label?) (? (listof label-exp?)))))
(define/pred label-syscall? (cons 'syscall (cons (? label?) (cons (? symbol?) (? (listof label-exp?))))))

(define (label-variable? x)
  (match x
    [(list 'var (? label?) (? variable?)) #t]
    [_ #f]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require rackunit))

(module+ test
  (check-true (label-if? `(if (label x) (app (label y) (+ (prim (label z) 1)
                                                          (prim (label a) 2)))
                              (prim (label b) 1)
                              (prim (label c) 2))))
  (check-true (label-rec? '(rec (label g1467506) f (x) (app (label g1467507) (f x)))))
  (check-false (label-if? `(if (+ 1 2) 2 3)))
  (check-true (if? `(if (+ 1 2) 2 3)))
  (check-false (if? `(if (+ 1 2) 2)))
  (check-true (λ? `(λ (x y z) (+ 1 2))))
  (check-false (λ? `(λ (x 1) 2))))

(module+ test
  (check-equal? (list-ref/set (list (set 1 2 3) (set 4 5 6)) 0) (set 1 2 3))
  (check-equal? (list-ref/set (list (set 1 2 3) (set 4 5 6)) 1) (set 4 5 6))
  (check-equal? (list-ref/set (list (set 1 2 3) (set 4 5 6)) 2) (set)))







