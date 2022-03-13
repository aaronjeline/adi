#lang racket
(provide get-backwards-slice display-graph new-graph add-edge (struct-out graph))
;; Right now we are storing both fowrads & backwards edges
;; Forward edges can probably be removed.

;; A Graph (A) is a (hash A -> (set A)) X (hash A -> (set A))
;; A Call-Context is a Graph Labels
(struct graph (forward-edges backward-edges))
(define (new-graph)
  (reset-memo!)
  (graph (hash) (hash)))

;; Add an edge to the graph
(define (add-edge g src dst)
  (define (update-adjs h from to)
    (define cur-adjs (hash-ref h from (set)))
    (hash-set h from (set-add cur-adjs to)))
  (match g
    [(graph forward-edges backward-edges)
     (graph
      (update-adjs forward-edges src dst)
      (update-adjs backward-edges dst src))]))

(define (add-edges g edges)
  (foldr (λ (next-edge g) (add-edge g (first next-edge) (second next-edge))) g edges))


                            

(define (∪ . xs)
  (if (empty? xs)
      (set)
      (apply set-union xs)))
    

(define (get-backwards-edges g l)
  (match g
    [(graph _ back-edges)
     (hash-ref back-edges l (set))]))

(module+ test
  (require rackunit)
  (define g (add-edges (new-graph) '((a b) (c b) (d b))))
  (check-equal?
   (get-backwards-edges g 'b)
   (set 'a 'c 'd)))

(define backwards-slice-memo (make-hash))
(define (reset-memo!)
  (set! backwards-slice-memo (make-hash)))

;; Find all nodes reachable moving backwards across edges
;; ie:
;;; a -> b -> c, backwards slice(c) = { c, b, a}
(define (get-backwards-slice g e)
  (get-backwards-slice/seen g e (set)))

(define (get-backwards-slice/seen g n seen)
  (cond
    [(in-memo? n) (get-from-memo n)]
    [(has-seen? n seen) (set n)]
    [else
     (let*
         [(can-directly-reach (set->list (get-backwards-edges g n)))
          (now-seen (set-add seen n))
          (backwards-slices (map (λ (n) (get-backwards-slice/seen g n now-seen)) can-directly-reach))
          (answer (set-add (apply ∪ backwards-slices) n))]
       (add-to-memo! n answer)
       answer)]))

(define (add-to-memo! n answer)
  (hash-set! backwards-slice-memo n answer))

(define (in-memo? n)
  (hash-has-key? backwards-slice-memo n))

(define (get-from-memo n)
  (hash-ref backwards-slice-memo n))

(define (has-seen? n seen)
  (set-member? seen n))

(module+ test
  (check-equal?
   (get-backwards-slice g 'b)
   (set 'b 'a 'c 'd))
  (define g′ (add-edges (new-graph)
                        `((a b)
                          (c b)
                          (b c)
                          (d c)
                          (e f))))
  (check-equal?
   (get-backwards-slice g′ 'c)
   (set 'a 'c 'b 'd))
  (check-equal?
   (get-backwards-slice (add-edges (new-graph)
                                   '((a b)
                                     (b a)))
                        'a)
   (set 'a 'b)))

;; TODO use env variables to make this more portable
(define DOT_LOCATION "/opt/homebrew/bin/dot")

(define (display-graph g)
  (define dotsrc (render-graph g))
  (define png (make-temporary-file "~a.png"))
  (define png-port (open-output-file png #:exists 'truncate))
  (define-values (sp out in err)
    (subprocess png-port #f #f DOT_LOCATION "-Tpng"))
  (displayln dotsrc in)
  ;(close-input-port out)

 
  (close-output-port in)
  (define errstring (port->string err))
  (close-input-port err)
  (close-output-port png-port)
  (subprocess-wait sp)
  (define status (subprocess-status sp))
  (printf "Subprocess status code: ~a" status)
  (unless (zero? status)
    (printf "Stderr says:\n~a" errstring))
  (system (format "open ~a" png)))
  
  


(define (render-graph g)
  (match g
    [(graph forwards _)
     (define rendered
       (apply append
              (for/list [(hash-entry (hash->list forwards))]
                (render-edge (car hash-entry) (cdr hash-entry)))))
     (string-join
      (append '("digraph {") rendered '("}"))
            
      "\n")]))

(define (render-edge src dsts)
  (for/list [(dst dsts)]
    (format "~a -> ~a;" src dst)))





