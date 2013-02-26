#lang scheme
(require test-engine/scheme-tests)
 
(define (ncons x y)
  (* (expt 2 x)
     (add1 (* 2 y))))

(define (nhd n)
  (if (odd? n)
      0
      (add1 (nhd (quotient n 2)))))

(define (ntl n)
  (quotient n (expt 2 (add1 (nhd n)))))

(define (nat->fun n)
  (if (zero? n)
      empty
      (cons (nhd n) 
            (nat->fun (ntl n)))))

(define (fun->nat ns)
  (if (empty? ns)
      0
      (ncons (first ns)
             (fun->nat (rest ns)))))

(check-expect (nhd 2008) 3)
(check-expect (ntl 2008) 125)
(check-expect (ncons 3 125) 2008)
(check-expect (nat->fun 2008) (list 3 0 1 0 0 0 0))
(check-expect (fun->nat '(3 0 1 0 0 0 0)) 2008)

(define (app nls1 nls2)
  (if (zero? nls1)
      nls2
      (ncons (nhd nls1) 
             (app (ntl nls1) nls2))))

(check-expect (nat->fun (app (ncons 1 (ncons 2 0))
                             (ncons 3 0)))
              (append (cons 1 (cons 2 empty))
                      (cons 3 empty)))

(define (pair z) (sub1 (ncons (car z) (cdr z))))
(define (unpair z) (cons (nhd (add1 z))
                         (ntl (add1 z))))

(check-expect 
 (map unpair (build-list 8 (λ (i) i)))
 '((0 . 0) (1 . 0) (0 . 1) (2 . 0) (0 . 2) (1 . 1) (0 . 3) (3 . 0)))
(check-expect 
 (map pair '((0 . 0) (1 . 0) (0 . 1) (2 . 0) (0 . 2) (1 . 1) (0 . 3) (3 . 0)))
 (build-list 8 (λ (i) i)))

(test)
