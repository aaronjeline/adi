#lang racket
(require "stdlib.rkt")

(define (loop)
  (begin
    (display ":> ")
    (let [(in (read-line))]
      (match (string-split in #\space)
        [(list "exit") 'goodbye]
        [(list "cd" dir) (change-dir dir)]
        [cmd (run-command cmd)]))))

(define (change-dir dir)
  (begin
    (chdir dir)
    (loop)))

(define (run-command args)
  (let [(name (car args))
        (pid (fork))]
    (if (zero? pid)
        (exec name args)
        (wait-for-child))))

(define (wait-for-child)
  (let [(exit-code (wait))]
    (if (zero? exit-code)
        (loop)
        (begin
          (displayln
           (string-append
            "Process exited w/ non-zero exit code: "
            (number->string exit-code)))
          (loop)))))



(loop)