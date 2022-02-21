#lang racket
(provide exp? variable? label-exp? label? define/pred prim? label-prim? label-variable?)
(module+ test
  (require rackunit))

(require (for-syntax racket/match))
(define-for-syntax (format-syntax stx fmt symb)
  (datum->syntax stx
                 (string->symbol
                  (format "label-~a" (syntax->datum symb)))))


(define-syntax (define/pred stx)
  (syntax-case stx ()
    [(_ name body)   
     #`(begin
         (define (name e)
           (match e
             [body #t]
             [_ #f])))]))


(define (variable? x)
  (and (symbol? x)
       (not (equal? x 'empty))))

(define (label-variable? x)
  (match x
    [(list 'var (? label?) (? variable?)) #t]
    [_ #f]))
    

(define (exp? e)
  ((or/c
    prim?
    variable?
    if?
    let?
    λ?
    rec?
    begin?
    syscall?
    (listof exp?)) e))

(define (prim? e)
  (match e
    [(? number?) #t]
    [(? boolean?) #t]
    [(? empty-symb?) #t]
    [_ #f]))


   
    
    

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
    (list/c app? label? (listof exp?))) e))

(define/pred label-prim? (list 'prim (? label?) (? prim?)))


(define (app? e)
  (equal? e 'app))
      

(define (empty-symb? s)
  (equal? s 'empty))










               
                                      

(define/pred label? (list 'label (? symbol?)))
(define/pred if? (list 'if (? exp?) (? exp?) (? exp?)))
(define/pred let? (list 'let (list (? symbol?) (? exp?)) (? exp?)))
(define/pred λ? (list 'λ (? (listof symbol?)) (? exp?)))
(define/pred rec? (list 'rec (? symbol?) (? (listof symbol?)) (? exp?)))
(define/pred begin? (cons 'begin (? (listof exp?))))
(define/pred syscall? (cons 'syscall (cons (? symbol?) (? (listof exp?)))))

(define/pred label-if? (list 'if (? label?) (? label-exp?) (? label-exp?) (? label-exp?)))
(define/pred label-let? (list 'let (? label?) (list (? symbol?) (? label-exp?)) (? label-exp?)))
(define/pred label-λ? (list 'λ (? label?) (? (listof symbol?)) (? label-exp?)))
(define/pred label-rec? (list 'rec (? label?) (? symbol?) (? (listof symbol?)) (? label-exp?)))
(define/pred label-begin? (cons 'begin (cons (? label?) (? (listof label-exp?)))))
(define/pred label-syscall? (cons 'syscall (cons (? label?) (cons (? symbol?) (? (listof label-exp?))))))


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



