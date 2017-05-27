#lang racket

(provide memo-fib)

(define memo (make-hash))

(define (check-memo n)
  (hash-ref memo n 'not-found))

(define (memo-fib n)
  (if (< n 2) n
    (let ((search-result (check-memo n)))
      (if (eq? search-result 'not-found)
        (let ((result (+ (memo-fib (- n 1)) (memo-fib (- n 2)))))
          (hash-set! memo n result) result)
        search-result))))
