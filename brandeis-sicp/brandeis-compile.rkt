#lang racket

;; compile : Exp EnvName -> (EnvVal Cont -> Val)
(define (compile exp env-names)
  (cond [(constant? exp) (λ (env-vals k) (k exp))]
        [(variable? exp)
         (let ((compiled-var (list 'var (lookup-variable exp env-names))))
           (λ (env-vals k)
             (list-ref env-vals (index-of compiled-var))))]
           
          #;
          [(letrec? exp)
           (compile-letrec (letrec-vars exp)
                           (letrec-vals exp)
                           (letrec-body exp)
                           env-names)]
          [(lambda? exp)
           (let ((compiled-lambda 
                  (list 'lambda
                        (compile (body exp)
                                 (cons (binder exp) env-names)))))
             (λ (env-vals k)
               (k (λ (x k)
                    ((code compiled-lambda) (cons x env-vals) k)))))
               
          [(if? exp)
           (let ((compiled-predicate (compile (predicate exp) env-names))
                 (compiled-then (compile (then-part exp) env-names))
                 (compiled-else (compile (else-part exp) env-names)))
             (λ (env-vals k)
               (compiled-predicate env-vals
                                  (λ (true?)
                                    (if true?
                                        (compiled-then env-vals k)
                                        (compiled-else env-vals k))))))]
           
           
           (cons 'if (compile-list (cdr exp) env-names))]
          [(sequence? exp)
           (cons 'begin (compile-list (cdr exp) env-names))]
          [(enter? exp)
           (cons 'enter (compile-list (cdr exp)
                                      (cons '*EXIT* env-names)))]
          [(exit? exp)
           (cons 'exit (compile-list (cdr exp) env-names))]
          [(application? exp)
           (list (compile (function-of exp) env-names)
                 (compile (argument-of exp) env-names))]))
  
;; eval : CExp EnvVal (Val -> Val) -> Val
(define (eval exp env fred)
  (cond [(constant? exp) (fred exp)]
        [(address? exp) (fred (list-ref env (index-of exp)))]
        [(if? exp)
         (eval (predicate exp) env
               (λ (true?)
                 (if true?
                     (eval (then-part exp) env fred)
                     (eval (else-part exp) env fred))))]
        [(lambda? exp)
         (fred (λ (x fred)
                 (eval (code exp) (cons x env) fred)))]
        [(enter? exp)
         (eval (enter-body exp) (cons fred env) fred)]        
        #;
        [(exit? exp)
         (eval (exit-body exp) env (lookup env '*EXIT*))]
        [(application? exp)
         (eval (function-of exp) env
               (λ (f)
                 (eval (argument-of exp) env
                       (λ (v)
                         (f v fred)))))]))
       

(define (compile-list exp env-names)
  (map (λ (e) (compile e env-names)) exp))

(define (compile-letrec vars vals body env-names) 
  (let ((new-env-names (append vars env-names)))
    (let ((compiled-vals
           (map (λ (val) (compile val new-env-names))
                vals))
          (body-code (compile body new-env-names)))
      (list 'letrec
            (zip-together vars compiled-vals)
            body-code))))

;; Exp -> Val
(define (try exp) 
  (eval (compile exp initial-names) initial-values (λ (x) x)))

(define (zip-together vars vals)
  (if (null? vars)
      '()
      (cons (cons (car vars) (list (car vals)))
            (zip-together (cdr vars) (cdr vals)))))

(define (lookup-variable v env-names)
  (if (null? env-names)
      v
      (if (eq? v (car env-names))
          0
          (let ((a (lookup-variable v (cdr env-names))))
            (if (number? a) (add1 a) a)))))

(define initial-names
  '(cons car cdr null? pair? zero?
         true false - * + = < 1+))
  
(define (unop op)
  (lambda (x k) (k (op x))))
(define (binop op)
  (lambda (x k) (k (lambda (y kk) (kk (op x y))))))

(define initial-values
  (list (binop cons)
        (unop car)  ;; (λ (x k) (k (car x))
        (unop cdr)
        (unop null?)
        (unop pair?)
        (unop zero?)
        #t
        #f
        (binop -)
        (binop +)
        (binop *)
        (binop =)
        (binop <)                          
        (unop add1)))
               
(define constant? integer?)
(define extend cons)
(define (variable? v) (not (pair? v))) 
(define (begins-with atom)
  (λ (exp)
    (if (pair? exp) (equal? (car exp) atom) #f)))
(define lambda? (begins-with 'lambda))
(define address? (begins-with 'var))
(define index-of cadr)
(define binder caadr)
(define body caddr)
(define code cadr)
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
(define letrec? (begins-with 'letrec))
(define (letrec-vars e) (map car (cadr e)))
(define (letrec-vals e) (map cadr (cadr e)))
(define (letrec-body e) (caddr e))
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