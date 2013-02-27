;; The first three lines of this file were inserted by DrRacket. They record metadata
;; about the language level of this file in a form that our tools can easily process.
#reader(lib "htdp-intermediate-lambda-reader.ss" "lang")((modname brandeis-fact) (read-case-sensitive #t) (teachpacks ()) (htdp-settings #(#t constructor repeating-decimal #f #t none #f ())))
;; Computes n!
;; Natural -> Natural
(define (factorial n)
  (if (= n 0)
      1
      (* n (factorial (- n 1)))))

(check-expect (factorial 5) 120)

;; Computes (k n!)
;; Natural (Natural -> Natural) -> Natural
(define (factorial/cps n k)
  (if (= n 0)
      (k 1)
      (factorial/cps (- n 1) 
                     (λ (n-1!)
                       (k (* n n-1!))))))
