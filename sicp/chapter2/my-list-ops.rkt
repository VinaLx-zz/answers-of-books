#lang racket

(provide (all-defined-out))

(define (my-last l)
  (if (empty? (rest l)) (first l) (my-last (rest l))))

(define (my-reverse l)
  (define (my-reverse-impl acc l)
    (if (empty? l) acc
        (my-reverse-impl (list* (first l) acc) (rest l))))
  (my-reverse-impl empty l))

(define (deep-reverse l)
  (define (deep-reverse-impl acc l)
    (if (empty? l) acc
        (let* ((temp (first l))
               (now (if (list? temp) (deep-reverse-impl empty temp) temp)))
          (deep-reverse-impl (list* now acc) (rest l)))))
  (deep-reverse-impl empty l))

(define (same-pairity x . xs)
  (let ((pairity (even? x)))
    (define (same-pairity-impl l)
      (if (empty? l) empty
          (let ((acc (same-pairity-impl (rest l)))
                (now (first l)))
            (if (equal? (even? now) pairity) (list* now acc) acc))))
    (list* x (same-pairity-impl xs))))

(define ((my-map f) l)
  (define (my-map-impl cur)
    (if (empty? cur) empty
        (list* (f (first l)) (my-map-impl (rest cur)))))
  (my-map-impl l))

(define ((my-foreach f) l) ((my-map f) l) (void))

(define ((deep-map f) l)
  (define (deep-map-impl l)
    (if (empty? l) empty
      (let* ((temp (first l))
             (cur (if (list? temp) (deep-map-impl temp) (f temp))))
        (list* cur (deep-map-impl (rest l))))))
  (deep-map-impl l))

(define (fringe t)
  (define (fringe-impl e)
    (if (list? e) (apply append (map fringe-impl e)) (list e)))
  (if (list? t) (fringe-impl t) (error 'fringe "fringe expect a list")))

(define (subsets l)
  (if (empty? l) (list empty)
      (let ((r (subsets (rest l))))
         (append r (map (λ (s) (list* (first l) s)) r)))))
