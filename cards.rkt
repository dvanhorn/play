#lang racket
(require rackunit)
;; A Card is a (card Number Suit)
;; A Suit is one of: '♥ '♣ '♠ '♦
;; A Number is a natural in [1,13].
(struct card (number suit) #:prefab)

;; reduce : [Listof Card] -> [Listof Card]
(define (reduce cards)
  (cond [(less-than-four? cards) cards]
        [(similar? (first cards) (fourth cards))
         (reduce (cons (first cards)
                       (list-tail cards 3)))]
        [else cards]))

;; play : [Listof Card] -> [Listof Card]
(define (play cards)
  (for/fold ([played empty])
    ([c cards])
    (reduce (cons c played))))

(define (less-than-four? cards)
  (< (length cards) 4))

;; Do the cards have the same number or suit?
(define (similar? c1 c2)
  (or (= (card-number c1) (card-number c2))
      (eq? (card-suit c1) (card-suit c2))))

(check-equal? (reduce '(#s(card 9 ♣)
                        #s(card 1 ♣)
                        #s(card 1 ♦)
                        #s(card 4 ♣)))              
              '(#s(card 9 ♣)
                #s(card 4 ♣)))

(check-equal? (play '(#s(card 9 ♣)
                      #s(card 1 ♣)
                      #s(card 1 ♦)
                      #s(card 4 ♣)))
              '(#s(card 4 ♣)
                #s(card 9 ♣)))

;; [List X] -> [List X]
(define (shuffle ls)
  (cond [(empty? ls) empty]
        [else
         (define-values (elem rest)
           (random-element ls))
         (cons elem (shuffle rest))]))

;; [List X] -> (values X [List X])
(define (random-element ls)
  (define (f i ls)
    (cond [(zero? i) (values (first ls) (rest ls))]
          [else
           (define-values (e es) (f (sub1 i) (rest ls)))
           (values e (cons (first ls) es))]))
  (f (random (length ls)) ls))

(define deck
  (for*/list ((s '(♥ ♣ ♠ ♦))
              (n (in-range 1 14)))
    (card n s)))

(play (shuffle deck))
