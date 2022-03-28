#lang racket
(require racket/trace)
(define-syntax-rule (letp (x y) d b)
  (match d
    [(cons x y) b]
    [e (error "Not a pair!: " e)]))

(struct store (next heap) #:transparent)
(struct env (frame next) #:transparent)
(struct pointer (loc type) #:transparent)
(struct cons-cell (car cdr) #:transparent)
(struct closure (params body frame) #:transparent)

(define (env-lookup ρ x)
  (if ρ
      (match (assoc x (env-frame ρ))
        [(list _ r) r]
        [#f (env-lookup (env-next ρ) x)])
      (error "Unknown Variable: " x)))

(define (bind ρ . args)
  (define frame
    (match args
      [(list (? list? f)) f]
      [(list (? list? names) (? list? vals)) (zip names vals)]
      [(list (? symbol? x) v) `((,x ,v))]))
  (env frame ρ))

(define (alloc t s)
  (match s
    [(store next heap)
     (cons (pointer next t) (store (add1 next) heap))]))

(define (deref p s)
  (hash-ref (store-heap s) (pointer-loc p)))

(define (write p v s)
  (modify-heap
   (λ (h)
     (hash-set h (pointer-loc p) v))
   s))

(define (modify-heap f s)
  (match s
    [(store next heap)
     (store next (f heap))]))

(define init-store (store 0 (hash)))

(define empty-env #f)

(define init-env (bind empty-env `((+ ,+) (* ,*) (= ,=) (sub1 ,sub1))))

(define (run e)
  (letp (v s) (eval e init-env init-store)
        (begin
          ;(displayln s)
          v)))

(module+ test
  (require rackunit)
  (check-equal? (run `(if #f #t #f)) #f)
  (check-equal? (run `(let ((x 5)) x)) 5)
  (check-equal? (run `((λ (x) (+ x 1)) 5)) 6)
  (check-equal?
   (run
    `(let ((fact (rec fact (x)
                  (if (= x 0)
                      1
                      (* x (fact (sub1 x)))))))
       (fact 5)))
   120)
  (check-equal? (run `(let ((add1 (let ((x 1)) (λ (y) (+ y x)))))
                        (add1 2))) 3)
  (check-equal?
   (run `(let ((p (box 3)))
           (begin
             (set-box! p 5)
             (unbox p))))
   5)
  (check-equal?
   (run `(car (cdr (cons 1 (cons 2 (cons 3 empty))))))
   2)
  (check-equal?
   (run `(let ((length (rec length (x)
                        (if (empty? x)
                            0
                            (+ 1 (length (cdr x)))))))
           (length (cons 1 (cons 2 (cons 3 empty))))))
   3)
  (check-equal?
   (run `(let ((foldr (rec foldr (f b xs)
                       (if (empty? xs)
                           b
                           (f (car xs) (foldr f b (cdr xs)))))))
           (let ((sum (λ (xs) (foldr + 0 xs))))
             (let ((map (λ (f xs) (foldr (λ (x ys) (cons (f x) ys)) empty xs))))
               (sum (map (λ (x) (+ x 1)) (cons 1 (cons 2 (cons 3 empty)))))))))
   9))

(define (eval e ρ s)
  (match e
    [(? self-evaluating?) (cons e s)]
    [(? variable? x) (cons (env-lookup ρ x) s)]
    [(? op1?) (eval-op1 (first e) (second e) ρ s)]
    [(? op2?) (eval-op2 (first e) (second e) (third e) ρ s)]
    [`(if ,e0 ,e1 ,e2)
     (letp (guard s0) (eval e0 ρ s)
           (eval (if guard e1 e2) ρ s0))]
    [`(let ((,x ,def)) ,body)
     (letp (v s0) (eval def ρ s)
           (let [(ρ0 (bind ρ x v))]
             (eval body ρ0 s0)))]
    [`(λ ,(? list? xs) ,def) (cons (build-closure xs def (set->list (free e)) ρ) s)]
    [`(rec ,f ,xs ,def)
     (cons (build-closure xs def (set->list (free e)) ρ) s)]
    [(cons 'begin es) (eval-begin es ρ s)]
    [(cons `syscall (cons name es))
     (printf "Syscall: ~a\n" name)
     (letp (_ s0) (eval-begin es ρ s)
           (cons (random 2) s0))]
    [(? list? app)
     (match (eval-app app ρ s)
       [(cons (cons fv argsv) s0)
        (apply-f fv argsv ρ s0)])]))

(define (apply-f f args ρ s)
  (match f
    [(? procedure?) (cons (apply f args) s)]
    [(closure params body frame)
     (define ρ0 (bind (bind ρ frame) (zip params args)))
     (eval body ρ0 s)]
    [_ (error "Application of non-function")]))
     
(define (eval-app app ρ s)
  (match app
    [(cons fe args)
     (letp (fv s0) (eval fe ρ s)
           (letp (argsv s1) (eval-args args ρ s0)
                 (cons (cons fv argsv) s1)))]
    ['() (error "Empty Application")]))

(define (eval-args args ρ s)
  (match args
    ['() (cons '() s)]
    [(cons arg args)
     (letp (argv s0) (eval arg ρ s)
           (letp (argsv s1) (eval-args args ρ s0)            
                 (cons (cons argv argsv) s1)))]))

(define (build-closure params def free_vars ρ)
  (define frame (zip free_vars (map (λ (x) (env-lookup ρ x)) free_vars)))
  (closure params def frame))

(define (eval-begin es ρ s)
  (match es
    [(cons e '()) (eval e ρ s)]
    [(cons e es)
     (letp (_ s0) (eval e ρ s)
           (eval-begin es ρ s0))]
    ['() (error "Empty Begin Form")]))

(define op1s (make-hash))
(define op2s (make-hash))

(define-for-syntax (format-symbol f selector stx)
  (string->symbol (format f (selector (syntax->datum stx)))))

(define-syntax (define-op stx)
  (syntax-case stx ()
    [(_ k name)
     (let [(fname (format-symbol "eval-~a" caddr stx))
           (ophash_name (format-symbol "op~as" cadr stx))]
       (with-syntax ([f (datum->syntax stx fname)]
                     [ophash (datum->syntax stx ophash_name)])
         (syntax
          (hash-set! ophash (quote name) f))))]))



(define (eval-box v ρ s)
  (letp (ptr s0) (alloc 'box s)
        (cons ptr (write ptr v s0))))

(define (eval-set-box! v1 v2 ρ s)
  (match v1
    [(? (λ (v) (pointer-kind v 'box)))
     (define s0 (write v1 v2 s))
     (cons v2 s0)]
    [_ (error "Type Error!")]))

(define (pointer-kind p t)
  (if (pointer? p)
      (eq? (pointer-type p) t)
      #f))
        

(define (eval-unbox v ρ s)
  (if (pointer-kind v 'box)
      (cons (deref v s) s)
      (error "Type Error")))

(define (eval-cons v1 v2 ρ s)
  (letp (ptr s0) (alloc 'cons s)
        (let [(s1 (write ptr (cons-cell v1 v2) s0))]
          (cons ptr s1))))


(define (cons-op o)
  (λ (v ρ s)
    (if (pointer-kind v 'cons)
        (match (deref v s)
          [(cons-cell car cdr)
           (o car cdr ρ s)])
        (type-error 'cons-op 'cons v))))
      
(define eval-car
  (cons-op (λ (car cdr ρ s)
             (cons car s))))
;(trace eval-car)
(define eval-cdr
  (cons-op (λ (car cdr ρ s)
             (cons cdr s))))
;(trace eval-cdr)

(define (eval-cons? v ρ s)
  (cons (pointer-kind v 'cons) s))

(define (eval-empty? v ρ s)
  (cons (eq? v 'empty) s))

(define-op 1 box)
(define-op 1 unbox)
(define-op 2 set-box!)
(define-op 2 cons)
(define-op 1 car)
(define-op 1 cdr)
(define-op 1 cons?)
(define-op 1 empty?)

(define (op1? e)
  (match e
    [(list (? (member? op1s)) _) #t]
    [_ #f]))

(define (op2? e)
  (match e
    [(list (? (member? op2s)) _ _) #t]
    [_ #f]))

(define (op1-e e) (second e))
(define (op2-e1 e) (second e))
(define (op2-e2 e) (third e))

(define (eval-op1 op e ρ s)
  (letp (v s0) (eval e ρ s)
        ((hash-ref op1s op) v ρ s0)))

        

(define (eval-op2 op e1 e2 ρ s)
  (letp (v1 s0) (eval e1 ρ s)
        (letp (v2 s1) (eval e2 ρ s0)
              ((hash-ref op2s op) v1 v2 ρ s1))))


(define (free e)
  (match e
    ['empty (set)]
    [(? number?) (set)]
    [(? boolean?) (set)]   
    [(? variable?) (set e)]
    [(? op1?) (free (op1-e e))]
    [(? op2?) (∪ (free (op2-e1 e)) (free (op2-e2 e)))]
    [`(if ,e0 ,e1 ,e2)
     (apply ∪ (map free (list e0 e1 e2)))]
    [`(let ((,x ,def)) ,body)
     (∪
      (free def)
      (set-subtract (free body) (set x)))]
    [`(λ ,(? list? xs) ,def) (set-subtract (free def) (apply set xs))]
    [`(rec ,f ,xs ,def) (set-subtract (free def) (apply set (cons f xs)))]
    [(cons 'begin es) (apply ∪ (map free es))]
    [(cons 'syscall (cons _ args))
     (apply ∪ (map free args))]
    [(? list? app) (apply ∪ (map free app))]))

(define (type-error loc t v)
  (error (format "~a: Type Error! Expected: ~a, Got: ~a" loc t (typeof v))))

(define (typeof v)
  (match v
    [(? number?) "number"]
    [(? boolean?) "boolean"]
    ['empty "empty"]
    [(pointer _ t) (format "pointer to ~a" t)]
    [_ (error "Invalid Value!")]))

(define (member? lst)
  (λ (x)
    (hash-has-key? lst x)))




(define (self-evaluating? e)
  (or (number? e) (boolean? e) (eq? 'empty e)))

(define variable? symbol?)

(define ∪ set-union)

(define (zip a b)
  (map list a b))


