#lang racket
(require redex)

(define-language ARITH
  [e n (e + e)]
  [n natural]
  
  [E hole (E + e) (n + E)]
  
  [k mt (K1 e k) (K2 n k)])


(define --->
  (reduction-relation 
   ARITH
   (--> (in-hole E_1 (n_1 + n_2))
        (in-hole E_1 ,(+ (term n_1) (term n_2))))))


(traces	--->	 
 	(term (3 + ((1 + 2) + 4))))

(define --->K
  (reduction-relation
   ARITH
   (--> (n_2 (K2 n_1 k)) (,(+ (term n_1) (term n_2)) k))
   (--> (n (K1 e k)) (e (K2 n k)))
   (--> ((e_1 + e_2) k) (e_1 (K1 e_2 k)))))

(traces --->K
        (term ((3 + ((1 + 2) + 4)) mt)))
   
   
   