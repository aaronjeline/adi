#lang racket
(require racket/trace threading "common.rkt" "labeller.rkt")


(define-syntax-rule (letpair (x y z) d b)
  (match d
    [(list x y z) b]
    [e (error "Not a pair!: " e)]))

(define-syntax-rule (pλ (x y z) b ...)
  (λ (p)
    (match p
      [(list x y z) (begin b ...)]
      [e (error "Not a pair!:" e)])))



(define (type? t)
  (match t
    ['box #t]
    ['cons #t]
    [_ #f]))

(define/contract (forall s f)
  (-> set? (-> any/c set?) set?)
  (apply ∪ (set->list (smap f s))))

(define/contract (smap f s)
  (-> procedure? set? set?)
  (~> s
      set->list
      (map f _)
      list->set))

(struct store (heap) #:transparent)
(struct env (frame next) #:transparent)
(struct pointer (loc type) #:transparent)
(struct cons-cell (car cdr) #:transparent)
(struct closure (params body frame) #:transparent)
(struct rec-closure (name params body frame) #:transparent)

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

(define/contract (alloc t label s)
  (-> type? label? store? (list/c pointer? (set/c symbol?) store?))
  (match s
    [(store heap)
     (list (pointer label t) (set) (store heap))]))

(define/contract (deref p s)
  (-> pointer? store? set?)
  (hash-ref (store-heap s) (pointer-loc p)))

(define (write p v s)
  (modify-key
   (λ (s)
     (set-add s v))
   p s))

(define (modify-key f p s)
  (modify-heap
   (λ (h)
     (let [(cur (hash-ref h (pointer-loc p) (set)))]
       (hash-set h (pointer-loc p) (f cur))))
   s))

(define (modify-heap f s)
  (match s
    [(store heap)
     (store (f heap))]))

(define init-store (store (hash)))


(define (set-map f s)
  (~> s
      set->list
      (map f _)
      list->set))


;; state : (list exp env state)
(define (env/c e)
  (match e
    [#f #t]
    [(env frame rest)
     (and (frame? frame)
          (env/c rest))]))
(define state/c (list/c any/c env/c store?))
(define seen? (set/c state/c))

(define (symbolic? v)
  (match v
    ['nat #t]
    ['empty #t]
    [_ #f]))
(define value?
  (or/c number? boolean? pointer? symbolic? closure? rec-closure? procedure?))
(define response? (set/c (list/c value? (set/c symbol?) store?)))

(define-syntax (define/simple stx)
  (syntax-case stx ()
    [(define-simple (o x y) b)
     (syntax (define/contract (o x y l s) (-> value? value? label? store? response?) (set-map (λ (r) (list r (set) s)) b)))]
    [(define-simple (o x) b)
     (syntax (define/contract (o x l s) (-> value? label? store? response?) (set-map (λ  (r) (list r (set) s)) b)))]))

(define-syntax (define/op stx)
  (syntax-case stx ()
    [(define/op (o x y l s) b)
     (syntax (define/contract (o x y l s) (-> value? value? label? store? response?) b))]
    [(define/op (o x l s) b)
     (syntax (define/contract (o x l s) (-> value? label? store? response?) b))]))

(define/simple (+^ a b)
  (set 'nat))

(define/simple (*^ a b)
  (set 'nat))

(define/simple (=^ a b)
  (if (and (number? a) (number? b))
      (set (= a b))
      (set #t #f)))
 

(define/simple (-^ a b)
  (set 'nat))

(define/simple (add1^ a)
  (set 'nat))

(define/simple (sub1^ a)
  (set 'nat))



(define/op (eval-box v l s)
  (letpair (ptr syscalls s0) (alloc 'box l s)
           (set (list ptr (set) (write ptr v s0)))))

(define/op (eval-set-box! v1 v2 l s)
  (match v1
    [(? (λ (v) (pointer-kind v 'box)))
     (define s0 (write v1 v2 s))
     (set (list v2 (set) s0))]
    [_ (error "Type Error!")]))

(define (pointer-kind p t)
  (if (pointer? p)
      (eq? (pointer-type p) t)
      #f))
        

(define/op (eval-unbox v l s)
  (if (pointer-kind v 'box)
      (forall (deref v s)
              (λ (unboxd)
                (set (list unboxd (set) s))))
      (error "Type Error")))

(define/op (eval-cons v1 v2 l s)
  (letpair (ptr syscalls s0) (alloc 'cons l s)
           (let [(s1 (write ptr (cons-cell v1 v2) s0))]
             (set (list ptr (set) s1)))))


(define (cons-op o)
  (λ (v l s)
    (if (pointer-kind v 'cons)
        (forall (deref v s)
                (λ (cc)
                  (match cc
                    [(cons-cell car cdr)
                     (o car cdr s)])))
       
        (type-error 'cons-op 'cons v))))
      
(define eval-car
  (cons-op (λ (car cdr s)
             (set (list car (set) s)))))
;(trace eval-car)
(define eval-cdr
  (cons-op (λ (car cdr s)
             (set (list cdr (set) s)))))
;(trace eval-cdr)

(define/contract (eval-cons? v l s)
  (-> value? label? store? response?)
  (set (list (pointer-kind v 'cons) (set) s)))

(define/contract (eval-empty? v l s)
  (-> value? label? store? response?)
  (set (list (eq? v 'empty) (set) s)))
  

(define empty-env #f)
(define init-env (bind empty-env `((+ ,+^) (* ,*^) (= ,=^) (- ,-^) (add1 ,add1^) (sub1 ,sub1^)
                                           (box ,eval-box) (unbox ,eval-unbox)
                                           (set-box! ,eval-set-box!)
                                           (cons ,eval-cons)
                                           (empty? ,eval-empty?)
                                           (car ,eval-car) (cdr ,eval-cdr))))






(define frame? (listof (list/c symbol? value?)))

(define syscall-map (make-hash))
(define (clear-syscall-map!)
  (set! syscall-map (make-hash)))
(define/contract (add-syscalls! l new-calls)
  (-> symbol? (set/c symbol?) void?)
  (define cur (hash-ref syscall-map l (set)))
  (hash-set! syscall-map l (∪ cur new-calls))
  (void))

(define/contract (query-syscalls e)
  (-> label-exp? set?)
  (hash-ref syscall-map (get-label e) (set)))

(define (run e (needs-labelling #t))
  (clear-syscall-map!)
  (define e_ (if needs-labelling (label-exp e) e))
  (smap car (eval e_ init-env init-store (set) (set))))

(define (run/dbg e)
  (eval (label-exp e) init-env init-store (set)))

(define/contract (run-and-get-mapping e)
  (-> label-exp? hash?)
  (run e #f)
  syscall-map)



(module+ test
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
  
  #;
  (check-mapping
   (app (label j)
        ((rec (label a) f (x) (if (label b) (app (label c)
                                                 ((var (label d) =)
                                                  (prim (label e) 1)
                                                  (syscall (label f) write (var (label g) x))))
                                  (prim (label h) 2)
                                  (app (label k) ((var (label l) f) (prim (label m) 1)))))
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
  (check-equal?
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
   (set 0 1)))






(define syscall-set? (set/c symbol?))





(define/contract (eval e ρ s current-syscalls seen)
  (-> label-exp? env/c store? syscall-set? seen? response?)
  (define this (list e ρ s))
  (if (set-member? seen this)
      (set)
      (eval-step e ρ s current-syscalls (set-add seen this))))

(define/contract (eval-step e ρ s current-syscalls seen)
  (-> exp? env/c store? syscall-set? seen? response?)
  ;(add-syscalls! (get-label e) current-syscalls)
  (match e
    [(? label-prim?) (set (list (get-prim e) (set) s))]
    [(? label-variable? x) (set (list (env-lookup ρ (get-variable x)) (set) s))]
    [`(if (label ,l) ,e0 ,e1 ,e2) (eval-if l e0 e1 e2 ρ s current-syscalls seen)]
    [`(let (label ,l) (,x ,def) ,body) (eval-let l x def body ρ s current-syscalls seen)]
    [`(λ ,(? label?) ,xs ,def) (set (list (build-closure xs def (set->list (free e)) ρ) (set) s))]
    [`(rec ,(? label?) ,f ,xs ,def)
     (set (list (build-recursive-closure f xs def e ρ) (set) s))]
    
    [(cons 'begin (cons `(label ,l) es)) (eval-begin l es ρ s current-syscalls seen)]
    [(cons `syscall (cons `(label ,l) (cons name es)))
     (eval-syscall l name es ρ s current-syscalls seen)]
    [(list 'app (? label? l) (? list? app))
     (eval-app app ρ l s current-syscalls seen)]))

  

(define/contract (eval-if l e0 e1 e2 ρ s cur-syscalls seen)
  (-> symbol? label-exp? label-exp? label-exp? env? store? syscall-set? seen? response?)
  (define guards (eval e0 ρ s cur-syscalls seen))
  (forall guards (pλ (v syscalls s0)
                     (define r (eval (if v e1 e2) ρ s0 (set) seen))
                     (add-syscalls! l (∪ (query-syscalls e0) (query-syscalls e1) (query-syscalls e2)))
                     r)))
                     

(define/contract (eval-let l x def body ρ s cur-syscalls seen)
  (-> symbol? symbol? any/c any/c env/c store? syscall-set? seen? response?)
  (define definitions (eval def ρ s cur-syscalls seen))
  (forall definitions
          (pλ (v syscalls_from_def s0)
              (define r
                (eval body (bind ρ x v) s0 (set) seen))
              (add-syscalls! l (∪ (query-syscalls def) (query-syscalls body)))
              r)))
          

          
(define/contract (eval-syscall label name es ρ s cur-syscalls seen)
  (-> symbol? symbol? (listof label-exp?) env/c store? syscall-set? seen? response?)
  (define results (eval-begin label es ρ s cur-syscalls seen))
  (forall results
          (pλ (r syscalls s0)
              (define all-syscalls (∪ syscalls (set name)))
              (add-syscalls! label all-syscalls)
              (for [(label (map get-label es))]
                (add-syscalls! label all-syscalls))
              (set (list 1 all-syscalls s0) (list 0 all-syscalls s0)))))
  
    


(define/contract (apply-f f args l s cur-syscalls seen)
  (-> any/c list? label? store? syscall-set? seen? response?)
  (match f
    [(? procedure?) (apply f (append args (list l s)))]
    [(closure params body frame)
     (define ρ0 (bind (bind empty-env frame) (zip params args)))
     (eval body ρ0 s cur-syscalls seen)]
    [(rec-closure fname params body frame)
     (define p0 (bind (bind empty-env frame) (zip (cons fname params) (cons f args))))
     (eval body p0 s cur-syscalls seen)]
    [_ (error "Application of non-function: " f)]))


(define/contract (eval-app app ρ l s cur-syscalls seen)
  (-> list? env/c label? store? syscall-set? seen? response?)
  (forall (eval-list-of-exprs (label->symbol l) app ρ s cur-syscalls seen)
          (pλ (vs syscalls s0)
              (match vs
                [(cons fv argsv)
                 (add-syscalls! (label->symbol l) syscalls)
                 (apply-f fv argsv l s0 syscalls seen)]
                ['() (error "Empty Application")]))))
          



(define/contract (build-closure params def free_vars ρ)
  (-> (listof symbol?) any/c (listof symbol?) env/c closure?)
  (define frame (zip free_vars (map (λ (x) (env-lookup ρ x)) free_vars)))
  (closure params def frame))

(define/contract (build-recursive-closure f xs def e ρ)
  (-> symbol? (listof symbol?) any/c any/c env/c rec-closure?)
  (match (build-closure xs def (set->list (free e)) ρ)
    [(closure params def frame)
     (rec-closure f params def frame)]))
;(set (cons (build-closure xs def (set->list (free e)) ρ) s)))

(define/contract (eval-begin l es ρ s cur-syscalls seen)
  (-> symbol? list? env/c store? syscall-set? seen? response?)
  (forall
   (eval-list-of-exprs l es ρ s cur-syscalls seen)
   (pλ (vs syscalls s0)
       (add-syscalls! l syscalls)
       (set (list (last vs) syscalls s0)))))
          

;; (list expr) ρ store seen -> (set (list exp))
(define/contract (eval-list-of-exprs l es ρ s cur-syscalls seen)
  (-> symbol? (listof label-exp?) env/c store? syscall-set? seen? (set/c (list/c list? (set/c symbol?) store?)))
  (define evaluation-result
    (match es
      ['() (set (list '() (set) s))]
      [(cons e es)
       (define results (eval e ρ s cur-syscalls seen))
       (forall results
               (pλ (v syscalls s0)
                   (forall (eval-list-of-exprs l es ρ s0 syscalls seen)
                           (pλ (vs syscalls s1)
                               (add-syscalls! (get-label e) syscalls)
                               (set (list (cons v vs) syscalls s1))))))]))
  (define syscalls (map query-syscalls es))
  (update-syscalls-in-list es syscalls)
  (when (not (empty? es))
    (add-syscalls! l (query-syscalls (first es))))
  evaluation-result)


;; Iterate over a list in reverse with idices
(define-syntax-rule (for/reverse/enumerate i [(x xs)] body)
  (for
      [(i (reverse (range (length xs))))
       (x (reverse xs))]
    body))
          


(define/contract (update-syscalls-in-list es syscalls)
  (-> (listof exp?) (listof set?) void?)
  (for/reverse/enumerate i
    [(e es)]
    (begin
      (define l (get-label e))
      (add-syscalls! l (list-ref/set syscalls (add1 i))))))

(define/contract (free e)
  (-> label-exp? set?)
  (match e
    [(? label-prim?) (set)]
    [(? label-variable?) (set (get-variable e))]
    [`(if ,(? label?) ,e0 ,e1 ,e2)
     (apply ∪ (map free (list e0 e1 e2)))]
    [`(let ,(? label?) (,x ,def) ,body)
     (∪
      (free def)
      (set-subtract (free body) (set x)))]
    [`(λ ,(? label?) ,xs ,def) (set-subtract (free def) (apply set xs))]
    [`(rec ,(? label?) ,f ,xs ,def) (set-subtract (free def) (apply set (cons f xs)))]
    [(cons 'begin
           (cons
            (? label?)
            es))
     (apply ∪ (map free es))]
    [(cons 'syscall (cons (? label?) (cons _ args)))
     (apply ∪ (map free args))]
    [(list 'app (? label?) (? list? app)) (apply ∪ (map free app))]))

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

(define (∪ . xs)
  (if (empty? xs)
      (set)
      (apply set-union xs)))

(define (zip a b)
  (map list a b))


