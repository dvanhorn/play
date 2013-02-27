#lang racket

(define (double n)
  (* n n))

(define (bin->num b)
  (match b
    ['() 0]
    [_     
     (define (loop b len-so-far)
       (match b
         ['() 1]
         [(cons b bs)
          (+ (loop bs (add1 len-so-far))
             (* b (expt 2 len-so-far)))]))
     (loop b 0)]))


(define (carry b)
  (match b
    ['() '(1)]
    [(cons 0 b)
     (cons 1 b)]
    [(cons 1 b)
     (cons 0 (carry b))]))

(define (bsuc b)
  (match b
    ['() (cons 0 '())]
    [(cons 1 b)
     (cons 0 (carry b))]
    [(cons 0 b)
     (cons 1 b)]))

(bin->num '(0))
(bin->num '(1))
(bin->num '(0 0))
(bin->num '(1 0))
(bin->num '(0 1))
(bin->num '(1 1))

(bsuc '())
(bsuc (bsuc '()))
(bsuc (bsuc (bsuc '())))
(bsuc (bsuc (bsuc (bsuc '()))))
(bsuc (bsuc (bsuc (bsuc (bsuc '())))))
(bin->num (bsuc (bsuc (bsuc (bsuc (bsuc (bsuc '())))))))

(define (flip b) (cond [(zero? b) 1] [else 0]))

(define (num->bin n)
  (cond [(zero? n) '()]
        [else
         (bsuc (num->bin (sub1 n)))]))

;; A "fast" implementation
#;
(define (num->bin n)
  (cond [(zero? n) '()]
        [else
         (define (loop n)
           (cond [(zero? n) '()]
                 [else
                  (cons (remainder n 2)
                        (loop (quotient n 2)))]))
         (loop (sub1 n))]))

(define (do-times f n)
  (cond [(zero? n) (λ (x) x)]
        [else (λ (x) (f ((do-times f (sub1 n)) x)))]))
         
(define (f n)
  (define b ((do-times bsuc n) '()))
  (printf "bin: ~a; nat: ~a; bin->nat ~a~n" b n (bin->num b)))



(define (sum-evens n)
  (* n (add1 n)))

(sum-evens 1)


