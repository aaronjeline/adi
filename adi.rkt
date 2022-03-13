#lang racket
(require threading racket/trace "common.rkt" "labeller.rkt" "graph.rkt")
(provide (all-defined-out))

(define-syntax-rule (letpair (x y z) d b)
  (match d
    [(list x y z) b]
    [e (error "Not a pair!: " e)]))

(define-syntax-rule (pλ (x y z w) b ...)
  (λ (p)
    (match p
      [(list x y z w) (begin b ...)]
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
(struct procedure-call-context
  (call-label
   last-label
   context-graph
   seen)
  #:transparent)

  

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
  (-> type? symbol? store? (list/c pointer? (set/c symbol?) store?))
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


;; A response is a set of evaluation results,
;; Each evaluation result is a
;; list
;;  0 -> the value produced
;;  1 -> the last label executed
;;  2 -> the context graph produced
;;  3 -> the store produced
(define response? (set/c (list/c value? symbol? graph? store?)))

(define-syntax (define/simple stx)
  (syntax-case stx ()
    [(define-simple (o x y) b)
     (syntax (define/contract (o xs ctxt)
               (-> (listof value?) procedure-call-context? response?)
               (match xs
                 [(list x y)
                  (match ctxt
                    [(procedure-call-context _ l context s)
                     (set-map (λ (r) (list r l context s)) b)])])))]
              
    [(define-simple (o x) b)
     (syntax (define/contract (o xs ctxt)
               (-> (listof value?) procedure-call-context? response?)
               (match xs
                 [(list x)
                  (match ctxt
                    [(procedure-call-context _ l context s)
                     (set-map (λ (r) (list r l context s)) b)])])))]))
              

(define-syntax (define/op stx)
  (syntax-case stx ()
    [(define/op (o cur-l x y l context s) b)
     (syntax (define/contract (o xs ctxt)
               (-> (listof value?) procedure-call-context? response?)
               (match xs
                 [(list x y)
                  (match ctxt
                    [(procedure-call-context cur-l l context s)
                     b])])))]
    [(define/op (o cur-l x l context s) b)
     (syntax (define/contract (o xs ctxt)
               (-> (listof value?) procedure-call-context? response?)
               (match xs
                 [(list x)
                  (match ctxt
                    [(procedure-call-context cur-l l context s)
                     b])])))]))

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



(define/op (eval-box cur-l v l context s)
  (letpair (ptr syscalls s0) (alloc 'box cur-l s)
           (set (list ptr l context (write ptr v s0)))))

(define/op (eval-set-box! cur-l v1 v2 l context s)
  (match v1
    [(? (λ (v) (pointer-kind v 'box)))
     (define s0 (write v1 v2 s))
     (set (list v2 l context s0))]
    [_ (error "Type Error!")]))

(define (pointer-kind p t)
  (if (pointer? p)
      (eq? (pointer-type p) t)
      #f))
        

(define/op (eval-unbox cur-l v l context s)
  (if (pointer-kind v 'box)
      (forall (deref v s)
              (λ (unboxd)
                (set (list unboxd l context s))))
      (error "Type Error")))

(define/op (eval-cons cur-l v1 v2 l context s)
  (letpair (ptr syscalls s0) (alloc 'cons cur-l s)
           (let [(s1 (write ptr (cons-cell v1 v2) s0))]
             (set (list ptr l context s1)))))



(define (cons-op o)
  (λ (vs ctxt)
    (match vs
      [(list v)
       (match ctxt
         [(procedure-call-context _ l context s)
          (if (pointer-kind v 'cons)
              (forall (deref v s)
                      (λ (cc)
                        (match cc
                          [(cons-cell car cdr)
                           (o l context car cdr s)])))
              (type-error 'cons-op 'cons v))])])))
      
(define eval-car
  (cons-op (λ (l context car cdr s)
             (set (list car l context s)))))

(define eval-cdr
  (cons-op (λ (l context car cdr s)
             (set (list cdr l context s)))))


(define/contract (eval-cons? vs ctxt)
  (-> (listof value?) procedure-call-context? response?)
  (match vs
    [(list v)
     (match ctxt
       [(procedure-call-context _ l context s)  
        (set (list (pointer-kind v 'cons) l context s))])]))

(define/contract (eval-empty? vs ctxt)
  (-> (listof value?) procedure-call-context? response?)
  (match vs
    [(list v)
     (match ctxt
       [(procedure-call-context _ l context s)  
        (set (list (eq? v 'empty) l context s))])]))
  

(define empty-env #f)
(define init-env (bind empty-env `((+ ,+^) (* ,*^) (= ,=^) (- ,-^) (add1 ,add1^) (sub1 ,sub1^)
                                           (box ,eval-box) (unbox ,eval-unbox)
                                           (set-box! ,eval-set-box!)
                                           (cons ,eval-cons)
                                           (empty? ,eval-empty?)
                                           (car ,eval-car) (cdr ,eval-cdr))))







(define frame? (listof (list/c symbol? value?)))

;; Map from program labels to sets of syscalls
(define syscall-map (make-hash))
;; Reset the syscall map
(define (clear-syscall-map!)
  (set! syscall-map (make-hash)))

;; Add a syscall into the syscall map and a particular label
(define/contract (add-syscalls! l new-calls)
  (-> symbol? (set/c symbol?) void?)
  (define cur (hash-ref syscall-map l (set)))
  (hash-set! syscall-map l (∪ cur new-calls))
  (void))

(define/contract (query-syscalls e)
  (-> label-exp? set?)
  (hash-ref syscall-map (get-label e) (set)))

(define (run/core e (needs-labelling #t))
  (clear-syscall-map!)
  (define e_ (if needs-labelling (label-exp e) e))
  (eval e_ init-env init-store (new-graph) (set)))

(define (run e (needs-labelling #t))
  (smap car (run/core e needs-labelling)))

;; TODO dlete
(define example
  `(app (label j)
      ((rec (label a) foo (x) (if (label b) (app (label c)
                                               ((var (label d) =)
                                                (prim (label e) 1)
                                                (syscall (label f) write (var (label g) x))))
                                (prim (label h) 2)
                                (app (label k) ((var (label l) foo) (prim (label m) 1)))))
       (prim (label n) 1))))


(define (run/dbg e)
  (eval (label-exp e) init-env init-store (set)))

(define/contract (run-and-get-mapping e)
  (-> label-exp? hash?)
  (run e #f)
  syscall-map)


(define syscall-set? (set/c symbol?))





(define/contract (eval e ρ s context seen)
  (-> label-exp? env/c store? graph? seen? response?)
  (define this (list e ρ s))
 ; (printf "Seen: ~a\n" seen)
  (if (set-member? seen this)
      (set)
      (eval-step e ρ s context (set-add seen this))))



(define/contract (eval-step e ρ s context seen)
  (-> exp? env/c store? graph? seen? response?)
  (match e
    [(? label-prim?) (set (list (get-prim e) (get-label e) context s))]
    [(? label-variable? x) (set (list (env-lookup ρ (get-variable x)) (get-label e) context s))]
    [`(if (label ,l) ,e0 ,e1 ,e2) (eval-if l e0 e1 e2 ρ s context seen)]
    [`(let (label ,l) (,x ,def) ,body) (eval-let l x def body ρ s context seen)]
    [`(λ (label ,l) ,xs ,def) (set (list (build-closure xs def (set->list (free e)) ρ) l context s))]
    [`(rec (label ,l) ,f ,xs ,def)
     (set (list (build-recursive-closure f xs def e ρ) l context s))]
    
    [(cons 'begin (cons `(label ,l) es)) (eval-begin l es ρ s context seen)]
    [(cons `syscall (cons `(label ,l) (cons name es)))
     (eval-syscall l name es ρ s context seen)]
    [(list 'app (? label? l) (? list? app))
     (eval-app app ρ l s context seen)]))

  

(define/contract (eval-if l e0 e1 e2 ρ s context seen)
  (-> symbol? label-exp? label-exp? label-exp? env? store? graph? seen? response?)
  (define context′ (add-edge context l (get-label e0)))
  (define guards (eval e0 ρ s context′ seen))
  (forall guards (pλ (v last-label context′′ s0)
                     (if v
                         (eval e1 ρ s0 (add-edge context′′ last-label (get-label e1)) seen)
                         (eval e2 ρ s0 (add-edge context′′ last-label (get-label e2)) seen)))))
                    
                     

(define/contract (eval-let l x def body ρ s context seen)
  (-> symbol? symbol? any/c any/c env/c store? graph? seen? response?)
  (define definitions (eval def ρ s (add-edge context l (get-label def)) seen))
  (forall definitions
          (pλ (v last-label context′ s0)     
              (eval body (bind ρ x v) s0 (add-edge context′ last-label (get-label body)) seen))))
             
          


(define/contract (eval-syscall label name es ρ s context seen)
  (-> symbol? symbol? (listof label-exp?) env/c store? graph? seen? response?)
  (define results (eval-begin label es ρ s (add-edge context label (get-label (first es))) seen))
  (forall results
          (pλ (r last-label context′ s0)
              (for [(node (get-backwards-slice context′ last-label))]
                (add-syscalls! node (set name)))
              (set (list 1 last-label context′ s0)
                   (list 0 last-label context′ s0)))))
  
    

(define/contract (apply-f cur-l f args l s context seen)
  (-> symbol? any/c list? symbol? store? graph? seen? response?)
  (match f
    [(? procedure?)
     (f args (procedure-call-context cur-l l context s))]
    [(closure params body frame)
     (define ρ0 (bind (bind empty-env frame) (zip params args)))
     (eval body ρ0 s (add-edge context l (get-label body)) seen)]
    [(rec-closure fname params body frame)
     (define p0 (bind (bind empty-env frame) (zip (cons fname params) (cons f args))))
     (eval body p0 s (add-edge context l (get-label body)) seen)]
    [_ (error "Application of non-function: " f)]))

;; Evlaute the funciton and all the arguments
;; Pass to apply-f to perform the application
(define/contract (eval-app app ρ l s context seen)
  (-> list? env/c label? store? graph? seen? response?)
  (forall (eval-list-of-exprs (label->symbol l) app ρ s context seen)
          (pλ (vs last-label context′ s0)
              (match vs
                [(cons fv argsv)
                 (apply-f (label->symbol l) fv argsv last-label s0 context′ seen)]
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


(define/contract (eval-begin l es ρ s context seen)
  (-> symbol? list? env/c store? graph? seen? response?)
  (forall
   (eval-list-of-exprs l es ρ s context seen)
   (pλ (vs last-label context′ s0)
       (set (list (last vs) last-label context′ s0)))))
          

;; (list expr) ρ store seen -> (set (list exp))
(define/contract (eval-list-of-exprs l es ρ s context seen)
  (-> symbol? (listof label-exp?) env/c store? graph? seen?
      (set/c (list/c list? symbol? graph? store?)))
  (match es
    ['() (set (list '() l context s))]
    [(cons e es)
     (define results (eval e ρ s (add-edge context l (get-label e)) seen))
     (forall results
             (pλ (v last-label context′ s0)
                 (forall (eval-list-of-exprs last-label es ρ s0 context′ seen)
                         (pλ (vs last-label context′′ s1)
                             (set (list (cons v vs) last-label context′′ s1))))))]))



;; Iterate over a list in reverse with idices
(define-syntax-rule (for/reverse/enumerate i [(x xs)] body ...)
  (for
      [(i (reverse (range (length xs))))
       (x (reverse xs))]
    (begin body ...)))
          


(define/contract (update-syscalls-in-list es syscalls)
  (-> (listof exp?) (listof set?) void?)
  (for/reverse/enumerate i [(e es)]
    (define l (get-label e))
    (add-syscalls! l (list-ref/set syscalls (add1 i)))))

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



