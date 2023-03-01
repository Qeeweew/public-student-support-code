#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let ([sym (gensym)])
            (Let sym ((uniquify-exp env) e) ((uniquify-exp (dict-set env x sym)) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (define (rco-exp e)
    (match e
      [(Let x ex body)
       (let ([exp1 (rco-exp ex)]
             [exp2 (rco-exp body)])
         (Let x exp1 exp2))]
      [(Prim op es)
       (let ([res (map rco-atom es)])
         (foldl (lambda (kv exp)
                  (Let (car kv) (cdr kv) exp))
                (Prim op (map car res))
                (apply append (map cdr res))))]
      [else e]))
  (define (rco-atom e) ; return an atom and Association Lists map sym to exp
    (match e
      [(Let x ex body)
       (let ([exp1 (rco-exp ex)]
             [exp2 (rco-exp body)]
             [y (gensym)])
         (cons (Var y)
               (list (cons y exp2) (cons x exp1))))]
      [(Prim op es)
       (let ([sym (gensym)]
             [res (map rco-atom es)])
         (cons
          (Var sym)
          (cons
           (cons sym (Prim op (map car res))) ; Prim op with atom
           (apply append (map cdr res)))))] ; concat list
      [else (cons e '())])) ;; Int or Var
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (define (explicate-tail e)
    (match e
      [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
      [else (Return e)])) ;; Var | Int | Prim
  (define (bind-let cont0 cont1 x) ; need to extract last return
    (match cont0
      [(Return val) (Seq (Assign (Var x) val) cont1)]
      [(Seq stmt tail) (Seq stmt (bind-let tail cont1 x))]))
  (define (explicate-assign e x cont)
    (match e
      [(Let y rhs body)
       (explicate-assign rhs y
                         (bind-let (explicate-tail body) cont x))] ; monad
      [else (Seq (Assign (Var x) e) cont)])) ;; Var | Int | Prim
  (match p
      [(Program info body) (CProgram info (list (cons 'start (explicate-tail body))))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (define (select-atm p)
    (match p
      [(Int x) (Imm x)]
      [(Var x) (Var x)]
      [else (error 'atm "~s" p)]))
  (define (select-stmt p)
    (match p
      [(Assign vx exp)
       (match exp
         [(Int _) (list (Instr 'movq (list (select-atm exp) vx)))]
         [(Var _) (list (Instr 'movq (list (select-atm exp) vx)))]
         [(Prim 'read '()) (list (Callq 'read_int 0))]
         [(Prim '- (list e)) (list (Instr 'movq (list (select-atm e) vx))
                                   (Instr 'negq (list vx)))]
         [(Prim '- (list e1 e2)) (list
                                  (Instr 'movq (list (select-atm e1) (Reg 'rax)))
                                  (Instr 'subq (list (select-atm e2) (Reg 'rax)))
                                  (Instr 'movq (list (Reg 'rax) vx)))] ;; no optimization yet
         [(Prim '+ (list e1 e2)) (list
                                  (Instr 'movq (list (select-atm e1) (Reg 'rax)))
                                  (Instr 'addq (list (select-atm e2) (Reg 'rax)))
                                  (Instr 'movq (list (Reg 'rax) vx)))])]
      [else (error 'stmt)]))
  (define (select-tail p)
    (match p
     [(Return exp)
       (append
        (match exp
          [(Int _) (list (Instr 'movq (list (select-atm exp) (Reg 'rax))))]
          [(Var _) (list (Instr 'movq (list (select-atm exp) (Reg 'rax))))]
          [(Prim 'read '()) (list (Callq 'read_int 0))]
          [(Prim '- (list e)) (list (Instr 'movq (list (select-atm e) (Reg 'rax)))
                                    (Instr 'negq (list (Reg 'rax))))]
          [(Prim '- (list e1 e2)) (list
                                   (Instr 'movq (list (select-atm e1) (Reg 'rax)))
                                   (Instr 'subq (list (select-atm e2) (Reg 'rax))))]
          [(Prim '+ (list e1 e2)) (list
                                   (Instr 'movq (list (select-atm e1) (Reg 'rax)))
                                   (Instr 'addq (list (select-atm e2) (Reg 'rax))))])
        (list (Jmp 'conclusion)))]
      [(Seq stmt tail)
           (append (select-stmt stmt) (select-tail tail))]
      [else (error 'tail)]))
  (match p
    [(CProgram info body)
     (X86Program info (list
                       (cons (caar body) (Block '() (select-tail (cdar body))))))]))
               
; (define (f p) (select-instructions (explicate-control (remove-complex-opera* (uniquify (parse-program p))))))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info body)
     (X86Program
      info
      (let* ([entry (cdar info)]
             [var-index (for/list
                            ([t (cdar info)]
                             [i (build-list (length entry) (lambda (x) (- (* (+ x 1) 8))))])
                          (cons (car t) i))])
        (define (assign-arg arg)
          (match arg
            [(Var x) (Deref 'rbp (dict-ref var-index x))]
            [else arg]))
        (define (assign-instr instr)
          (match instr
            [(Instr op es) (Instr op (map assign-arg es))]
            [else instr]))
        (define (assign-block block)
          (match block
            [(Block info instrs) (Block info (map assign-instr instrs))]))
        (map (lambda (t) ;; label . block
               (cons (car t) (assign-block (cdr t))))
             body)))]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (define (assign-instr instr)
    (match instr
      [(Instr op (list (Deref reg1 x1) (Deref reg2 x2)))
       (list (Instr 'movq (list (Deref reg1 x1) (Reg 'rax)))
             (Instr op (list (Reg 'rax) (Deref reg2 x2))))]
      [(Instr op (list (Imm y) (Deref reg x)))  ; don't know x86 details yet
       (list (Instr 'movq (list (Imm y) (Reg 'rax)))
             (Instr op (list (Reg 'rax) (Deref reg x))))]
      [else (list instr)]))
  (define (assign-block block)
        (match block
          [(Block info instrs) (Block info (apply append (map assign-instr instrs)))]))
  (match p
    [(X86Program info body)
     (X86Program
      info
      (map (lambda (t) ;; label . block
             (cons (car t) (assign-block (cdr t))))
           body))]))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info body)
     (let* ([stack-size (* (length (car info)) 8)]
            [prelude (cons 'main
                           (Block '()
                                  (list
                                   (Instr 'pushq (list (Reg 'rbp)))
                                   (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                                   (Instr 'subq (list (Imm stack-size) (Reg 'rsp)))
                                   (Jmp 'start))))]
            [conclusion (cons 'conclusion
                              (Block '()
                                     (list
                                      (Instr 'addq (list (Imm stack-size) (Reg 'rsp)))
                                      (Instr 'popq (list (Reg 'rbp)))
                                      (Retq))))])
       (X86Program info (cons prelude (cons conclusion body))))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
