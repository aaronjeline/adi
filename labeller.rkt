#lang racket
(require "common.rkt")
(provide (contract-out (label-exp (-> exp? label-exp?))))



#;
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

(define (new-label)
  (list 'label (gensym)))

(define (label-exp e)
  (match e
    [(? integer?) e]
    [(? boolean?) e]
    [(? symbol?) e]
    ['empty 'empty]
    [(list 'if e0 e1 e2) (list 'if (new-label) (label-exp e0) (label-exp e1) (label-exp e2))]
    [`(let (,x ,def) ,body) `(let ,(new-label) (,x ,(label-exp def)) ,(label-exp body))]
    [`(λ ,xs ,def) `(λ ,(new-label) ,xs ,(label-exp def))]
    [`(rec ,name ,xs ,def) `(rec ,(new-label) ,name ,xs ,(label-exp def))]
    [(cons 'begin es)
     (cons 'begin
           (cons (new-label)
                 (for/list [(e es)]
                   (label-exp e))))]
    [(cons 'syscall (cons (? symbol? call) rst))
     (cons 'syscall
           (cons
            (new-label)
            (cons
             call
             (for/list [(e rst)]
               (label-exp e)))))]
    [(? list? es)
     (list 'app (new-label) (for/list [(e es)]
                              (label-exp e)))]))

(define (get-label e)
  (match e
    [(? number?) #f]
    [(? boolean?) #f]
    [(? variable?) #f]
    ['empty #f]
    [`(if (label ,l) ,_ ,_ ,_) l]
    [`(let (label ,l) ,_ ,_) l]
    [`(λ (label ,l) ,_ ,_) l]
    [`(rec (label ,l) ,_ ,_ ,_) l]
    [(cons 'begin (cons `(label ,l) _)) l]
    [(cons 'syscall (cons `(label ,l) _)) l]
    [`(app (label ,l) ,_) l]))


   

  
