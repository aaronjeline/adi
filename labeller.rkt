#lang racket
(require "common.rkt")
(provide (contract-out (label-exp (-> exp? label-exp?))))

(define (label-exp e)
  (define label 0)
  (define (labeller e)
    (match e
      [(? integer?) e]
      [(? boolean?) e]
      [(? symbol?) e]
      
      ))
  (labeller e))
  
