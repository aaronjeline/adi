#lang racket
(require "adi.rkt")

(require rackunit)
(require (for-syntax rackunit racket/set))
(define-syntax (check-mapping stx)
  (syntax-case stx ()
    [(_ e kvs)
     #`(let [(mapping (run-and-get-mapping (quote e)))]
         (for [(kv (quote kvs))]             
           (check-equal?
            (hash-ref mapping (car kv) (set))
            (apply set (cdr kv))
            (symbol->string (car kv)))))]))
    
          
  

(check-mapping (syscall (label a) write (prim (label c) 1) (prim (label b) 2)) ((a . (write))
                                                                                (c . (write))
                                                                                (b . (write))))

(check-mapping (let (label a)
                 (x (syscall (label b) write (prim (label c) 1) (prim (label d) 2)))
                 (var (label e) x))
               ((a . (write))
                (b . (write))
                (c . (write))
                (d . (write))
                (e . ())))

(check-mapping
 (app (label z)
      ((λ (label a) (x) (syscall (label b) write (var (label c) x)))
       (prim (label d) 1)))
 ((z . (write))
  (d . (write))
  (b . (write))
  (c . (write))))
  

(check-mapping
 (app (label j)
      ((rec (label a) foo (x) (if (label b) (app (label c)
                                               ((var (label d) =)
                                                (prim (label e) 1)
                                                (syscall (label f) write (var (label g) x))))
                                (prim (label h) 2)
                                (app (label k) ((var (label l) foo) (prim (label m) 1)))))
       (prim (label n) 1)))
 ((m . (write))))

  
(check-mapping
 (begin (label a)
        (syscall (label b) write (prim (label c) 1))
        (prim (label d) 2))
 ((a . (write)) (b . (write)) (c . (write)) (d . ())))
          

  
(check-mapping (app (label a) ((var (label z) +) (prim (label x) 1)
                                                 (syscall (label b) write
                                                          (prim (label y) 1)
                                                          (prim (label w) 2))))
                 
               ((a . (write))
                (z . (write))
                (x . (write))
                (b . (write))
                (y . (write))
                (w . (write))))
       
(check-mapping
 (syscall (label a)
          write
          (syscall (label b) read (prim (label b) 1) (prim (label c) 2))
          (prim (label d) 2))
 ((a . (write read))
  (b . (write read))))
  
; Recursion tests

; Recursive store test 
(check-equal? (run `((rec f (x) (f (cons 1 x))) empty)) (set))
  
(check-equal? (run `((rec f (x) (f x)) 1)) (set))
  
(check-equal?
 (run `((rec f (x) (if (= 1 (syscall write x 2))
                       2
                       (f 1))) 1)) (set 2))
  
(check-equal?
 (run `((rec f (x) (f (add1 x))) 1)) (set))

  
(check-equal? (run `((rec f (x)
                       (if (= x 0)
                           #t
                           (f (- x 1))))
                     2))
              (set #t))
  
(check-equal?
 (run `((rec f (x)
          (if (= (add1 x) (add1 5))
              2
              (f x))) 1))
 (set 2))
  
(check-equal?
 (run `((rec f (x)
          (cons x (f x))) empty))
 (set))
   
(check-equal? (run `(if #f #t #f)) (set #f))
(check-equal? (run `(let (x 5) x)) (set 5))
(check-equal? (run `((λ (x) (+ x 1)) 5)) (set 'nat))
(check-equal? (run `(if (= 1 (add1 1)) 1 0)) (set 1 0))
  
(check-equal?
 (run
  `(let (fact (rec fact (x)
                (if (= x 0)
                    1
                    (* x (fact (sub1 x))))))
     (fact 5)))
 (set 'nat))
(check-equal? (run `(let (add1 (let (x 1) (λ (y) (+ y x))))
                      (add1 2))) (set 'nat))
(check-equal?
 (run `(let (p (box 3))
         (begin
           (set-box! p 5)
           (unbox p))))
 (set 3 5))
(check-true
 (match (run `(cdr (cons 1 (cons 2 empty))))
   [(? set? s) (= (set-count s) 1)]))
   
   
#;(check-equal?
   (run `(car (cdr (cons 1 (cons 2 (cons 3 empty))))))
   (set 2))
(check-equal?
 (run `(let (length (rec length (x)
                      (if (empty? x)
                          0
                          (+ 1 (length (cdr x))))))
         (length (cons 1 (cons 2 (cons 3 empty))))))
 (set 'nat))
(check-equal?
 (run `(let (foldr (rec foldr (f b xs)
                     (if (empty? xs)
                         b
                         (f (car xs) (foldr f b (cdr xs))))))
         (let (sum (λ (xs) (foldr + 0 xs)))
           (let (map (λ (f xs) (foldr (λ (x ys) (cons (f x) ys)) empty xs)))
             (sum (map (λ (x) (+ x 1)) (cons 1 (cons 2 (cons 3 empty)))))))))
 (set 'nat))
(check-equal?
 (run `(syscall write 1))
 (set 0 1))
