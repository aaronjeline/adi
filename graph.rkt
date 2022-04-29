#lang racket
(require "common.rkt")
(provide neighbors get-backwards-slice display-graph new-graph add-edge (struct-out graph)
         merge-graphs*)
;; Right now we are storing both fowrads & backwards edges
;; Forward edges can probably be removed.

;; A Graph (A) is a (hash A -> (set A)) X (hash A -> (set A))
;; A Call-Context is a Graph Labels
(struct graph (starting-edge forward-edges backward-edges))
(define (new-graph starting)
  (graph starting (hash) (hash)))

;;given a graph g and a vertex n returns the neighbors of n
(define/contract (neighbors n g)
  (-> symbol? graph? (set/c symbol?))
  (hash-ref (graph-backward-edges g) n (set))) ;; WHY IS IT FORWARD AND NOT BACKWARD EDGES? AUTH2

;; Add an edge to the graph
(define (add-edge g src dst)
  (define (update-adjs h from to)
    (define cur-adjs (hash-ref h from (set)))
    (hash-set h from (set-add cur-adjs to)))
  (match g
    [(graph s forward-edges backward-edges)
     (graph s
            (update-adjs forward-edges src dst)
            (update-adjs backward-edges dst src))]))

;;adds multipl edges to the given graph
(define (add-edges g edges)
  (foldr (λ (next-edge g) (add-edge g (first next-edge) (second next-edge))) g edges))

;;merges two graphs into one graph
(define (merge-graphs g1 g2)
  (match (cons g1 g2)
    [(cons (graph s1 forward1 backward1)
           (graph s1 forward2 backward2))
     (graph s1 (merge forward1 forward2)
            (merge backward1 backward2))]
    [_ (error "Attempted to merge graphs without same starting edge!")]))
     

(define (merge-graphs* . gs)
  (match gs
    ['() (error "Empty merge!")]
    [(cons g _)
     (foldr (λ (g′ g) (merge-graphs g′ g)) (new-graph (graph-starting-edge g)) gs)]))

(define (merge h1 h2)
  (define h (make-hash))
  (add-all-to-hash! h h1)
  (add-all-to-hash! h h2)
  h)

(define (add-all-to-hash! h h′)
  (for [(entry (hash->list h′))]
    (match entry
      [(cons k v)
       (hash-set-union! h k v)])))
  
     

  


    

(define (get-backwards-edges g l)
  (match g
    [(graph _  _ back-edges)
     (hash-ref back-edges l (set))]))


;; Find all nodes reachable moving backwards across edges
;; ie:
;;; a -> b -> c, backwards slice(c) = { c, b, a}
(define (get-backwards-slice g e)
  (get-backwards-slice/seen g e (set)))

(define (get-backwards-slice/seen g n seen)
  (cond
    [(has-seen? n seen) (set n)]
    [else
     (let*
         [(can-directly-reach (set->list (get-backwards-edges g n)))
          (now-seen (set-add seen n))
          (backwards-slices (map (λ (n) (get-backwards-slice/seen g n now-seen)) can-directly-reach))
          (answer (set-add (apply ∪ backwards-slices) n))]
       answer)]))

(define (has-seen? n seen)
  (set-member? seen n))

(define (hash-set-union! h k v)
  (hash-update! h k (λ (s) (set-union s v)) (set)))

               
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Display graph
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO use env variables to make this more portable
(define DOT_LOCATION "/opt/homebrew/bin/dot")


(define (display-graph g)
  (define dotsrc (render-graph g))
  (define png (make-temporary-file "~a.png"))
  (define png-port (open-output-file png #:exists 'truncate))
  (define-values (sp out in err)
    (subprocess png-port #f #f DOT_LOCATION "-Tpng"))
  (displayln dotsrc in)
  (close-output-port in)
  (define errstring (port->string err))
  (close-input-port err)
  (close-output-port png-port)
  (subprocess-wait sp)
  (define status (subprocess-status sp))
  (unless (zero? status)
    (begin
      (printf "Subprocess status code: ~a" status)
      (printf "Stderr says:\n~a" errstring)))
  (system (format "open ~a" png))
  (void))
  
  
(define (render-graph g)
  (match g
    [(graph _ forwards _)
     (define rendered
       (apply append
              (for/list [(hash-entry (hash->list forwards))]
                (render-edge (car hash-entry) (cdr hash-entry)))))
     (define entry-node (format "~a [color = red]" (graph-starting-edge g)))
     (string-join
      (append '("digraph {") rendered `(,entry-node "}"))
            
      "\n")]))

(define (render-edge src dsts)
  (for/list [(dst dsts)]
    (format "~a -> ~a;" src dst)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(module+ test
  (require rackunit)
  (define g (add-edges (new-graph 'a) '((a b) (c b) (d b))))
  (check-equal?
   (get-backwards-edges g 'b)
   (set 'a 'c 'd)))

(module+ test
  (check-equal?
   (get-backwards-slice g 'b)
   (set 'b 'a 'c 'd))
  (define g′ (add-edges (new-graph 'a)
                        `((a b)
                          (c b)
                          (b c)
                          (d c)
                          (e f))))
  (check-equal?
   (get-backwards-slice g′ 'c)
   (set 'a 'c 'b 'd))
  (check-equal?
   (get-backwards-slice (add-edges (new-graph 'a)
                                   '((a b)
                                     (b a)))
                        'a)
   (set 'a 'b))
  (check-equal?
   (get-backwards-slice (add-edges (new-graph 'a)
                                   '((a b)
                                     (b c)
                                     (c a))) 'c)
   (set 'a 'b 'c))
  (define looping-example
    (add-edges
     (new-graph 'a)
     `((j a)
       (a n)
       (n b)
       (b c)
       (c d)
       (d e)
       (e f)
       (f g)
       (g h)
       (g k)
       (k l)
       (l m)
       (m b))))
  (check-equal?
   (get-backwards-slice looping-example 'm)
   (apply set '(m l k g f e d c b n a j))))