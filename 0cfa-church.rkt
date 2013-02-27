#lang racket

;; 0CFA in the AAM style on some hairy Church numeral churning

;; Moral: per machine-state store polyvariance is not viable,
;; but with widening it's not so bad.

;; (X -> Set X) -> (Set X) -> (Set X)
(define ((appl f) s)
  (for/fold ([i (set)])
    ([x (in-set s)])
    (set-union i (f x))))

;; (X -> Set X) (Set X) -> (Set X)
;; Calculate fixpoint of (appl f).
(define (fix f s)
  (let loop ((accum (set)) (front s))
    (if (set-empty? front)
        accum
        (let ((new-front ((appl f) front)))
          (loop (set-union accum front)
                (set-subtract new-front accum))))))

;; An Exp is one of:
;; (var Lab Exp)
;; (num Lab Number)
;; (bln Lab Boolean)
;; (lam Lab Sym Exp)
;; (app Lab Exp Exp)
;; (rec Sym Lam)
;; (if Lab Exp Exp Exp)
(struct exp (lab)            #:transparent)
(struct var exp (name)       #:transparent)
(struct num exp (val)        #:transparent)
(struct bln exp (b)          #:transparent)
(struct lam exp (var exp)    #:transparent)
(struct app exp (rator rand) #:transparent)
(struct rec (name fun)       #:transparent)
(struct ife exp (t c a)      #:transparent)
(struct 1op exp (o a)        #:transparent)
(struct 2op exp (o a b)      #:transparent)

;; A Val is one of:
;; - Number
;; - Boolean
;; - (clos Lab Sym Exp Env)
;; - (rlos Lab Sym Sym Exp Env)
(struct clos (l x e ρ)   #:transparent)
(struct rlos (l f x e ρ) #:transparent)

;; A Cont is one of:
;; - 'mt
;; - (ar Exp Env Cont)
;; - (fn Val Cont)
;; - (ifk Exp Exp Env Cont)
;; - (1opk Opr Cont)
;; - (2opak Opr Exp Env Cont)
;; - (2opfk Opr Val Cont)
(struct ar (e ρ k)      #:transparent)
(struct fn (v k)        #:transparent)
(struct ifk (c a ρ k)   #:transparent)
(struct 1opk (o k)      #:transparent)
(struct 2opak (o e ρ k) #:transparent)
(struct 2opfk (o v k)   #:transparent)

;; State
(struct state (σ)            #:transparent)
(struct ev state (e ρ k)     #:transparent)
(struct co state (k v)       #:transparent)
(struct ap state (f a k)     #:transparent)
(struct ap-op state (o vs k) #:transparent)
(struct ans state (v)        #:transparent)

(define (lookup ρ σ x)
  (hash-ref σ (hash-ref ρ x)))
(define (get-cont σ l)
  (hash-ref σ l))
(define (extend ρ x v)
  (hash-set ρ x v))
(define (join σ a s)
  (hash-set σ a
            (set-union s (hash-ref σ a (set)))))

(define-syntax-rule
  (do x <- se e)
  (for/set ([x se])
           e))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Machine

;; State -> Set State
(define (step state) 
  ;(printf "~a~n" state)
  (match state
    [(ev σ e ρ k)
     (match e
       [(var l x)           (do v <- (lookup ρ σ x)
                              (co σ k v))]
       [(num l n)           (set (co σ k n))]
       [(bln l b)           (set (co σ k b))]
       [(lam l x e)         (set (co σ k (clos l x e ρ)))]
       [(rec f (lam l x e)) (set (co σ k (rlos l f x e ρ)))]
       [(app l f e)
        (define-values (σ* a) (push state))
        (set (ev σ* f ρ (ar e ρ a)))]
       [(ife l e0 e1 e2)
        (define-values (σ* a) (push state))
        (set (ev σ* e0 ρ (ifk e1 e2 ρ a)))]
       [(1op l o e)
        (define-values (σ* a) (push state))
        (set (ev σ* e ρ (1opk o a)))]
       [(2op l o e f)
        (define-values (σ* a) (push state))
        (set (ev σ* e ρ (2opak o f ρ a)))])]

    [(co σ k v)
     (match k
       ['mt (set (ans σ v))]
       [(ar e ρ l) (set (ev σ e ρ (fn v l)))]
       [(fn f l)   (do k <- (get-cont σ l)
                     (ap σ f v k))]
       [(ifk c a ρ l)
        (do k <- (get-cont σ l)
          (ev σ (if v c a) ρ k))]
       [(1opk o l)
        (do k <- (get-cont σ l)
          (ap-op σ o (list v) k))]
       [(2opak o e ρ l)
        (set (ev σ e ρ (2opfk o v l)))]
       [(2opfk o u l)
        (do k <- (get-cont σ l)
          (ap-op σ o (list v u) k))])]
 
    [(ap σ fun a k)
     (match fun
       [(clos l x e ρ)
        (define-values (ρ* σ*) (bind state))
        (set (ev σ* e ρ* k))]
       [(rlos l f x e ρ)
        (define-values (ρ* σ*) (bind state))
        (set (ev σ* e ρ* k))]
       [_ (set state)])]

    [(ap-op σ o vs k)
     (match* (o vs)
       [('zero? (list (? number? n))) (set (co σ k (zero? n)))]
       [('sub1 (list (? number? n)))  (set (co σ k (widen (sub1 n))))]
       [('add1 (list (? number? n)))  (set (co σ k (widen (add1 n))))]
       [('zero? (list 'number))
        (set (co σ k #t)
             (co σ k #f))]
       [('sub1 (list 'number)) (set (co σ k 'number))]
       [('* (list (? number? n) (? number? m)))
        (set (co σ k (widen (* m n))))]
       [('* (list (? number? n) 'number))
        (set (co σ k 'number))]
       [('* (list 'number 'number))
        (set (co σ k 'number))]
       [(_ _) (set state)])]

    [_ (set state)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Concrete semantics
#;#;#;
(define (widen b)
  (cond [(number? b) b]
        [else (error "Unknown base value" b)]))

(define (bind s)
  (match s
    [(ap σ (clos l x e ρ) v k)
     (define a
       (add1 (for/fold ([i 0])
               ([k (in-hash-keys σ)])
               (max i k))))
     (values (extend ρ x a)
             (extend σ a (set v)))]
    [(ap σ (rlos l f x e ρ) v k)
     (define a
       (add1 (for/fold ([i 0])
               ([k (in-hash-keys σ)])
               (max i k))))
     (define b (add1 a))
     (values (extend (extend ρ x a) f b)
             (join (join σ a (set v)) b (set (rlos l f x e ρ))))]))

(define (push s)
  (match s
    [(ev σ e ρ k)
     (define a
       (add1 (for/fold ([i 0])
               ([k (in-hash-keys σ)])
               (max i k))))
     (values (join σ a (set k))
             a)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 0CFA-style Abstract semantics

(define (widen b)
  (cond [(number? b) 'number]
        [else (error "Unknown base value" b)]))

(define (bind s)
  (match s
    [(ap σ (clos l x e ρ) v k)
     (values (extend ρ x x)
             (extend σ x (set v)))]
    [(ap σ (rlos l f x e ρ) v k)
     (values (extend (extend ρ x x) f f)
             (join (join σ x (set v)) f (set (rlos l f x e ρ))))]))

(define (push s)
  (match s
    [(ev σ e ρ k)
     (define a (exp-lab e))
     (values (join σ a (set k))
             a)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Exp -> Set Val
;; 0CFA without store widening
(define (aval e)
  (for/set ([s (fix step (inj e))]
            #:when (ans? s))
           (ans-v s)))

;; Exp -> Set Vlal
;; 0CFA with store widening
(define (aval^ e)
  (for/fold ([vs (set)])
    ([s (fix wide-step (inj-wide e))])
    (set-union vs
               (match s
                 [(cons cs σ)
                  (for/set ([c cs]
                            #:when (ans^? c))
                           (ans^-v c))]))))

;; Exp -> Set State
(define (inj e)
  (set (ev (hash) e (hash) 'mt)))

;; Exp -> Set State^
(define (inj-wide e)
  (set (cons (set (ev^ e (hash) 'mt)) (hash))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Widening State to State^

;; State^ = (cons (Set Conf) Store)

;; Conf
(struct ev^ (e ρ k)     #:transparent)
(struct co^ (k v)       #:transparent)
(struct ap^ (f a k)     #:transparent)
(struct ap-op^ (o vs k) #:transparent)
(struct ans^ (v)        #:transparent)

;; Conf Store -> State
(define (c->s c σ)
  (match c
    [(ev^ e ρ k) (ev σ e ρ k)]
    [(co^ k v)   (co σ k v)]
    [(ap^ f a k) (ap σ f a k)]
    [(ap-op^ o vs k) (ap-op σ o vs k)]
    [(ans^ v) (ans σ v)]))

;; State -> Conf
(define (s->c s)
  (match s
    [(ev _ e ρ k) (ev^ e ρ k)]
    [(co _ k v)   (co^ k v)]
    [(ap _ f a k) (ap^ f a k)]
    [(ap-op _ o vs k) (ap-op^ o vs k)]
    [(ans _ v) (ans^ v)]))

;; Store Store -> Store
(define (join-store σ1 σ2)
  (for/fold ([σ σ1])
    ([k×v (in-hash-pairs σ2)])
    (hash-set σ (car k×v)
              (set-union (cdr k×v)
                         (hash-ref σ (car k×v) (set))))))

;; Set State -> Store
(define (join-stores ss)
  (for/fold ([σ (hash)])
    ([s ss])
    (join-store σ (state-σ s))))

;; State^ -> { State^ }
(define (wide-step state)
  (match state
    [(cons cs σ)
     (define ss (for/set ([c cs]) (c->s c σ)))
     (define ss* ((appl step) ss))
     (set (cons (for/set ([s ss*]) (s->c s))
                (join-stores ss*)))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parser

(define (parse sexp)
  (match sexp
    [`(let* () ,e) (parse e)]
    [`(let* ((,x ,e) . ,r) ,b)
     (app (gensym)
          (lam (gensym) x (parse `(let* ,r ,b)))
          (parse e))]
    [`(lambda (,x) ,e)
     (lam (gensym) x (parse e))]
    [`(if ,e0 ,e1 ,e2)
     (ife (gensym) (parse e0) (parse e1) (parse e2))]
    [`(rec ,f ,e)
     (rec f (parse e))]
    [`(sub1 ,e)
     (1op (gensym) 'sub1 (parse e))]
    [`(add1 ,e)
     (1op (gensym) 'add1 (parse e))]
    [`(zero? ,e)
     (1op (gensym) 'zero? (parse e))]
    [`(* ,e0 ,e1)
     (2op (gensym) '* (parse e0) (parse e1))]
    [`(,e0 ,e1)
     (app (gensym)
          (parse e0)
          (parse e1))]
    [(? boolean? b) (bln (gensym) b)]
    [(? number? n) (num (gensym) n)]
    [(? symbol? s) (var (gensym) s)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Computing with Church numerals

(define P
  ;; Ian's example, curried, alpha renamed and
  ;; let* in place of define where possible.
  '(let* ((plus (lambda (p1)
                  (lambda (p2)
                    (lambda (pf)
                      (lambda (x) ((p1 pf) ((p2 pf) x)))))))
          (mult (lambda (m1)
                  (lambda (m2)
                    (lambda (mf) (m2 (m1 mf))))))
          (pred (lambda (n)
                  (lambda (rf)
                    (lambda (rx)
                      (((n (lambda (g) (lambda (h) (h (g rf)))))
                        (lambda (ignored) rx))
                       (lambda (id) id))))))
          (sub (lambda (s1)
                 (lambda (s2)
                   ((s2 pred) s1))))

          (church0 (lambda (f0) (lambda (x0) x0)))
          (church1 (lambda (f1) (lambda (x1) (f1 x1))))
          (church2 (lambda (f2) (lambda (x2) (f2 (f2 x2)))))
          (church3 (lambda (f3) (lambda (x3) (f3 (f3 (f3 x3))))))
          (church0? (lambda (z) ((z (lambda (zx) #f)) #t)))
          (church=? (rec c=?
                      (lambda (e1)
                        (lambda (e2)
                          (if (church0? e1)
                              (church0? e2)
                              (if (church0? e2)
                                  #f
                                  ((c=? ((sub e1) church1)) ((sub e2) church1)))))))))

     ;; multiplication distributes over addition
     ((church=? ((mult church2) ((plus church1) church3)))
      ((plus ((mult church2) church1)) ((mult church2) church3)))))

(aval^ (parse P))