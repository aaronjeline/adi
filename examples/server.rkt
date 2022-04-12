#lang racket
(require "stdlib.rkt")

(define port 1337)

(define servSock (socket))

(bind-and-listen servSock port)

(define (loop)
  (let [(client (accept servSock))]
    (begin
      (handle-client client)
      (loop))))

(define (handle-client client)
  (let [(v (vector 0 0 0 0 0))]
    (begin
      (read-bytes client v)
      (displayln "Got msg: ")
      (displayln (vector->string v))
      (write-bytes client v)
      (close client))))

(loop)