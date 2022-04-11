#lang racket
(require "graph.rkt")
(provide find-pledges)

(module+ test
  (require rackunit))

(define (find-pledges g syscall-map)
  (find-pledges-step (graph-starting-edge g) g syscall-map (set)))

(module+ test
  (define g (add-edge (new-graph 'a) 'a 'b))
  (define syscall-map (make-hash))
  (hash-set! syscall-map 'a (set 'read))
  (check-equal?
   (find-pledges g syscall-map)
   (list (cons 'a (list 'read))))
  (displayln "---")
  (set! g
        (add-edge
         (add-edge (new-graph 'a) 'a 'b)
         'a 'c))
  (set! syscall-map (make-hash))
  (hash-set! syscall-map 'a (set 'read 'write))
  (hash-set! syscall-map 'b (set 'write))
  (check-equal? (find-pledges g syscall-map)
                (list (cons 'a (list 'read))
                      (cons 'b (list 'write)))))
  

(define (find-pledges-step n g syscall-map seen)
  (define now-seen (set-add seen n))
  (define (not-seen? x)
    (not (set-member? now-seen x)))
  (define next-syscalls
    (apply union
           (for/list [(neighbor (neighbors n g))]
             (hash-ref syscall-map neighbor (set)))))
  (define my-syscalls (hash-ref syscall-map n (set)))
  (define diff (set-subtract my-syscalls next-syscalls))
  (printf "Label: ~a syscalls: ~a\nnext-syscalls: ~a,diff: ~a\n" n my-syscalls next-syscalls diff)
  (define rest
    (apply append
           (for/list [(neighbor (filter not-seen? (set->list (neighbors n g))))]
             (find-pledges-step neighbor g syscall-map now-seen))))
  (if (set-empty? diff)
      rest
      (cons (build-pledge-entry n diff) rest)))
            

(define (build-pledge-entry label syscalls)
  (cons label (set->list syscalls)))
  

(define (union . xs)
  (if (empty? xs)
      (set)
      (apply set-union xs)))