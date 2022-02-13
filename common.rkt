#lang racket
(provide exp? label-exp? label? define/pred)
(module+ test
  (require rackunit))

(define (exp? e)
  ((or/c
    number?
    boolean?
    symbol?
    empty-symb?
    if?
    let?
    λ?
    rec?
    begin?
    syscall?
    (listof exp?)) e))

(define (label-exp? e)
  ((or/c
    number?
    boolean?
    symbol?
    empty-symb?
    label-if?
    label-let?
    label-λ?
    label-rec?
    label-begin?
    label-syscall?
    (list/c app? label? (listof exp?))) e))

(define (app? e)
  (equal? e 'app))
      

(define (empty-symb? s)
  (equal? s 'empty))


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

(define-syntax (define/label stx)
  (syntax-case stx ()
    [(_ name)
     (begin
       (define label-name (format-syntax stx "label-~a" #'name))
       #`(define (#,label-name e)
           (match e
             [(cons form-name
                    (cons
                     (list (quote label) (? symbol?))
                     rest))
              (name (cons form-name rest))]
             [_ #f])))]))

               
                                      

(define/pred label? (list 'label (? symbol?)))
(define/pred if? (list 'if (? exp?) (? exp?) (? exp?)))
(define/pred let? (list 'let (list (? symbol?) (? exp?)) (? exp?)))
(define/pred λ? (list 'λ (? (listof symbol?)) (? exp?)))
(define/pred rec? (list 'rec (? symbol?) (? (listof symbol?)) (? exp?)))
(define/pred begin? (cons 'begin (? (listof exp?))))
(define/pred syscall? (cons 'syscall (cons (? symbol?) (? (listof exp?)))))

(define/label if?)
(define/label let?)
(define/label λ?)
(define/label rec?)
(define/label begin?)
(define/label syscall?)


(module+ test
  (check-true (label-if? `(if (label x) (+ 1 2) 2 3)))
  (check-false (label-if? `(if (+ 1 2) 2 3)))
  (check-true (if? `(if (+ 1 2) 2 3)))
  (check-false (if? `(if (+ 1 2) 2)))
  (check-true (λ? `(λ (x y z) (+ 1 2))))
  (check-false (λ? `(λ (x 1) 2))))



