#lang racket

;; eval : Exp Env -> Val
#;
(define (eval exp env)
  (cond [(constant? exp) exp]
        [(variable? exp) (lookup env exp)]
        [(define? exp) '...]
        [(if? exp)
         (if (eval (predicate exp) env)
             (eval (then-part exp) env)
             (eval (else-part exp) env))]
        [(enter? exp) '...]
        [(exit? exp) '...]
        [(lambda? exp) 
         (λ (x) 
           (eval (body exp) (extend (binder exp) x env)))]
        [(application? exp) 
         ((eval (function-of exp) env) 
          (eval (argument-of exp) env))]))

;; eval : Exp Env (Val -> Val) -> Val
(define (eval exp env fred)
  (cond [(constant? exp) (fred exp)]
        [(variable? exp) (fred (lookup env exp))]
        [(error? exp) (list 'in-red: (cadr exp))]
        [(if? exp)
         (eval (predicate exp) env
               (λ (true?)
                 (if true?
                     (eval (then-part exp) env fred)
                     (eval (else-part exp) env fred))))]
        [(lambda? exp)
         (fred (λ (x fred)
              (eval (body exp) (extend (binder exp) x env) fred)))]
        [(enter? exp)
         (eval (enter-body exp) (extend '*EXIT* fred env) fred)]
        [(exit? exp)
         (eval (exit-body exp) env (lookup env '*EXIT*))]
        [(application? exp)
         (eval (function-of exp) env
               (λ (f)
                 (eval (argument-of exp) env
                       (λ (v)
                         (f v fred)))))]))
         
         
         
         
         
         



#;
(define (try exp)
  (eval exp init-env))


(define (extend var val env) (cons (cons var val) env))
(define (lookup env var)
  (cond ((null? env) (error "Unbound variable"))
        ((eq? (caar env) var) (cdar env))
        (else (lookup (cdr env) var))))

(define (unop op)
  (lambda (x k) (k (op x))))

(define (binop op)
  (lambda (x k) (k (lambda (y kk) (kk (op x y))))))

;; Think about this.
#;
(define (nop op n)
  (cond [(= n 1) (lambda (x wilma) (wilma (op x)))]
        [(> n 1) (lambda (x k)
                   ((nop op (sub1 n)) x k))]))

(define initial-global-environment
  (extend 'cons (binop cons)
    (extend '- (binop -)
      (extend '* (binop *)
        (extend '+ (binop +)
          (extend '= (binop =)
            (extend '< (binop <)
              (extend '1+ (unop add1) '()))))))))

(define init-env
  (extend '= (λ (x) (λ (y) (= x y)))
          (extend '+ (λ (x) (λ (y) (+ x y))) 
                  '())))


(define (try exp)
  (eval exp
        initial-global-environment
        initial-continuation))

(define (initial-continuation x) x)
  
(define constant? integer?)

(define (variable? v) (not (pair? v))) 
(define (begins-with atom)
  (lambda (exp)
    (if (pair? exp) (equal? (car exp) atom) #f)))
(define lambda? (begins-with 'lambda))
(define binder caadr)
(define body caddr)
(define define? (begins-with 'define)) 
(define define-of car)
(define (rest-of exp)
  (if (null? (cddr exp)) (cadr exp)
      (cdr exp))) 
(define def-name cadr)
(define (def-body exp)
  (if (null? (cdddr exp)) 
      (caddr exp)
      (cddr exp)))
(define if? (begins-with 'if))
(define predicate cadr) 
(define else-part cadddr) 
(define then-part caddr)
(define sequence? (begins-with 'begin)) 
(define first-exp car)
(define (rest-exps exp)
  (let ((r (cdr exp)))
    (if (pair? r)
(if (null? (cdr r)) (car r) r) r)))
(define enter? (begins-with 'enter)) 
(define exit? (begins-with 'exit))
(define enter-body cadr)
(define exit-body cadr)
(define (application? exp) 
  (if (pair? exp)
      (not ((begins-with 'define) (car exp))) #f))
(define function-of car) 
(define argument-of cadr)
(define (error? exp)
  ((begins-with 'error) exp))
        
  