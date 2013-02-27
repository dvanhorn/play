#lang racket

;; Wand-style type inference for λ-calculus + numbers,
;; uses source location as the source of fresh type variable
;; names to achieve determinism for constraint inference.

;; Syntax
(struct exp (l))
(struct vbl exp (x))
(struct lam exp (x e))
(struct app exp (e0 e1))
(struct num exp (n))

;; Type constructors
(define (→ a b) (list '→ a b))
(define nat '(nat))

;; Constraint constructors
(struct ≡ (x y) #:transparent)

;; Type environments
;; Uses function application notation for lookup and extension
;; (Γ x) = Γ(x)
;; (Γ x τ) = Γ[x → τ]
(struct env (ht)
  #:property prop:procedure
  (case-lambda
    [(m x)   (hash-ref (env-ht m) x)]
    [(m x τ) (env (hash-set (env-ht m) x τ))]))

(define Γ0 (env (hash)))

;; Restrict Γ to free variables of e
(define (↓ Γ e)
  (env (for/hash ([x (in-set (fv e))])
         (values x (Γ x)))))

;; Exp -> [Setof Id]
(define (fv e)
  (match e
    [(num l n) (set)]
    [(vbl l x) (set x)]
    [(lam l x e)
     (set-remove (fv e) x)]
    [(app l e0 e1)
     (set-union (fv e0) (fv e1))]))

;; [Env Id Type] Exp Type -> [Setof Constraint] G
(define (action-table Γ e t)
  (match e
    [(num l n) (values (set (≡ t nat)
                            ; Extra
                            (≡ l t))
                       (set))]
    [(vbl l x) (values (set (≡ t (Γ x))
                            ; Extra
                            ;; Why does this screw things up?
                            #;(≡ l t)) 
                       (set))]
    [(app l e0 e1)
     (let ((τ (exp-l e0)))
       (values (set (≡ l t)) ; Extra 
               (set (list (↓ Γ e0) e0 (→ τ t))
                    (list (↓ Γ e1) e1 τ))))]
    [(lam l x e)
     (let ((τ1 x)
           (τ2 (exp-l e)))
       (values (set (≡ t (→ τ1 τ2))
                    ; Extra
                    (≡ l t))
               (set (list (↓ (Γ x τ1) e) e τ2))))]))

;;; -----
#;
(define (action-table-clos Γ c t)
  (match c
    [(cons (num n) ρ) (values (set (≡ t nat)) (set))]
    [(cons (vbl x) ρ) (action-table-clos Γ (ρ x) t)]
    ...))
;;; -----

;; [Setof X] -> X [Setof X]
(define (set-choose s)
  (values (set-first s) (set-rest s)))

;; Exp -> [Setof Constraint]
(define (infer e)
  (let loop ((E (set))
             (G (set (list Γ0 e 0))))
    (if (set-empty? G)
        E
        (let ()
          (define-values (E* G*) (apply action-table (set-first G)))
          (loop (set-union E E*)
                (set-union (set-rest G) G*))))))

;; [Setof Constraint] -> [Setof Constraint]
(define (solve cs)
  (cond [(set-empty? cs) (set)]
        [else      
         (define-values (c cs*) (set-choose cs))
         (match c 
           [(≡ (list-rest C ts0)
               (list-rest C ts1))
            (unless (= (length ts0) (length ts1))
              (error "fail"))
            (solve (set-union (apply set (map ≡ ts0 ts1))
                              cs*))]
           [(≡ (list-rest C ts0)
               (list-rest D ts1))
            (error "fail:" C D)]
           [(or (≡ (list-rest C ts) t)
                (≡ t (list-rest C ts)))
            (set-add (solve (subst (cons C ts) t cs*))
                     (≡ t (cons C ts)))]
           [(≡ t t)
            (solve cs*)]
           [(≡ t s)
            (set-add (solve (subst s t cs*))
                     (≡ t s))])]))

;; Type TVar [Setof Constraint] -> [Setof Substitution]
(define (subst τ t cs)
  (for/set ([c cs]) (subst-one τ t c)))

;; Type TVar Constraint -> Constraint
(define (subst-one τ t c)
  (match c
    [(≡ t0 t1)
     (≡ (subst-type τ t t0)
        (subst-type τ t t1))]))

;; Type TVar Type -> Type
(define (subst-type τ t t0)
  (match t0
    [(list-rest C ts)
     (cons C (map (λ (ti) (subst-type τ t ti)) ts))]
    [_ (cond [(eq? t0 t) τ]
             [else t0])]))

;; [Setof Substitution] -> Type
(define (get-type soln)
  (define top
    (for/first ([s (in-set soln)]
                #:when (match s 
                         [(≡ 0 t) #t]
                         [_ #f]))
      (match s [(≡ 0 t) t])))
  (for/fold ([top top])
    ([s (in-set soln)])
    (match s 
      [(≡ t τ) (subst-type τ t top)])))

;; Exp -> Type
(define (typeof e)
  (get-type (solve (infer e))))

(require rackunit)
(check-equal? (subst-type 'a 'b 'c) 'c)
(check-equal? (subst-type 'a 'b 'b) 'a)
(check-equal? (subst-type 'a 'b (→ 'b 'c)) (→ 'a 'c))

(typeof (lam 0 'x (lam 1 'z (vbl 2 'x))))

(define wand-example
  (lam 0 'x (lam 1 'y (lam 2 'z
                           (app 3 (app 4 (vbl 5 'x) (vbl 6 'z))
                                (app 7 (vbl 8 'y) (vbl 9 'z)))))))

(infer wand-example)
(typeof wand-example)



(typeof (lam 0 'x (num 1 5)))

(typeof (lam 0 'x (lam 1 'y (vbl 2 'x))))
(typeof (lam 0 'x (lam 1 'y (vbl 2 'y))))

(typeof (lam 0 'x (app 1 (vbl 2 'x) (num 3 5))))


'infer
(infer (lam 0 'x (lam 1 'y (vbl 2 'x))))
(infer (lam 0 'x (lam 1 'y (vbl 2 'y))))

'solve
(solve (infer (lam 0 'x (lam 1 'y (vbl 2 'x)))))
(solve (infer (lam 0 'x (lam 1 'y (vbl 2 'y)))))

(solve (infer (lam 0 'x (lam 1 'y (num 2 6)))))

(infer (lam 0 'x (app 1 (lam 2 'y (vbl 3 'y)) (vbl 4 'x))))