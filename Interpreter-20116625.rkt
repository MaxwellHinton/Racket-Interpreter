; Maxwell Hinton 20116625 -- Interpreter final project.

#lang racket
(require eopl/eopl)

;; SLLGEN Lexcial Specification ----------------------------------
(define scanner-spec-1
  '((white-sp ((arbno (or #\space #\newline #\tab #\return))) skip)
    (comment ("//" (arbno (not #\newline))) skip)

    ; identifiers/names $x etc...
    (name ((or letter "_" "$")
                 (arbno (or letter digit "_" "$"))) symbol)

    ; string
    (string ("\"" (arbno (or letter digit " " "," "." "\"" "'" "!" "?")) "\"") string)

    ; Numbers.
    (number ((arbno digit)) number) ; postive integer
    (number ((arbno digit) "." (arbno digit)) number) ; postitive float

    (minus ("-") symbol)
    ))

;; SLLGEN Grammar ----------------------------------
(define grammar-1
  '(
    ; main program rule
    (program (statements) a-program)

    ; statements, which make up a program
    (statements (statement statements) statements-list)
    (statements () epsilon-statements)

    ; individual statements
    (statement (expression ";") expr-stmt)
    (statement ("const" name "=" expression ";") const-stmt)
    (statement (if-statement) if-statement-stmt)
    (statement ("function" name "(" names ")" block) function-decl-stmt) ;; declaring a function
    (statement ("return" expression ";") return-stmt)

    ; if statement
    (if-statement ("if" "(" expression ")" block "else" else-branch) if-stmt)

    ; else-branch
    (else-branch (block) else-block)
    (else-branch (if-statement) else-if-stmt)

    ; names and name-prime -- names-primes handles multiple names for argument purposes etc
    (names (name name-prime) names-list)
    (names () epsilon-names)
    (name-prime ("," name name-prime) names-list-prime)
    (name-prime () epsilon-name-prime)

    ; block
    (block ("{" statements "}") block-stmt)

    ; expressions
    (expression (term expression-prime) expr)
    (expression-prime ("+" term expression-prime) add-exp)
    (expression-prime ("-" term expression-prime) sub-exp)

    ; conditional stuff
    (expression-prime (">" term expression-prime) gt-exp)  ;; Greater than
    (expression-prime ("<" term expression-prime) lt-exp)  ;; Less than
    (expression-prime (">=" term expression-prime) gte-exp)  ;; Greater or equal
    (expression-prime ("<=" term expression-prime) lte-exp)  ;; Less or equal
    (expression-prime ("===" term expression-prime) eql-exp) ;; equal
    (expression-prime ("!==" term expression-prime) not-eql-exp) ;; not equal
    (expression-prime ("?" expression ":" expression) ternary-exp) ;; ternary operation
    (expression-prime ("||" term expression-prime) or-exp) ;; logical OR
    (expression-prime ("&&" term expression-prime) and-exp) ;; logical AND
    (expression-prime () epsilon-expr-prime)

    ; Term
    (term (factor term-prime) trm)
    (term-prime ("*" factor term-prime) mult-exp)
    (term-prime ("/" factor term-prime) div-exp)
    (term-prime ("%" factor term-prime) mod-exp)
    (term-prime () epsilon-term-prime)
    
    ;; Factors -- Mostly terminals
    (factor (number) const-exp)
    (factor (string) string-exp)
    (factor ("(" expression ")") paren-exp)
    (factor ("!" factor) not-exp) ;; logical NOT
    (factor ("-" factor) neg-exp) ;; negative
    (factor ("true") true-exp)
    (factor ("false") false-exp)

    ; Name or call factor is used to distinguish function calls from name calls.
    (factor (name-or-call) name-or-call-factor-exp)

    ; The distinction is based on what name-or-call-prime is:
    (name-or-call (name name-or-call-prime) name-or-call-exp)
    (name-or-call-prime ("(" argument-expressions ")") function-call-exp) ; Function call
    (name-or-call-prime () epsilon-call-prime) ; Constant/variable call

    ; arguments/parameters are expressions seperated by commas
    (argument-expressions (expression argument-expressions-prime) argument-list)
    (argument-expressions () epsilon-argument-expressions) ;; allows for empty arguments
    (argument-expressions-prime ("," expression argument-expressions-prime) argument-list-prime)
    (argument-expressions-prime () epsilon-argument-list)
    ))

(sllgen:make-define-datatypes scanner-spec-1 grammar-1)

(define scan&parse
  (sllgen:make-string-parser scanner-spec-1 grammar-1))

;; ----------------------------------Environment Definition ------------------------------

;; Global hashset was used to define the environment.
(define global-env (make-hash))

(define apply-env
  (lambda (name)
    (if (hash-has-key? global-env name)
        (hash-ref global-env name)
        (report-no-binding-found name))))

(define extend-env
  (lambda (name value)
    (hash-set! global-env name value)
    global-env))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

;; ----------------------------------Datatype Defintions --------------------------------

;; Return value datatype
(define-datatype return-value return-value?
  (a-return-value
   (value any/c)))

(define return-value-value
  (lambda (value)
    (cases return-value value
      (a-return-value (value) value))))

;; Closure datatype to handle functions
(define-datatype closure closure?
  (a-closure
   (params (list-of symbol?))
   (body block?)
   (env hash?)))

(define make-closure
  (lambda (params body env)
    (a-closure params body env)))


;; Expval datatype to wrap raw data into objects.
; In this interpreter I only wrap values when adding to the environment. 
(define-datatype expval expval?
  
  (num-val
   (num number?))
  
  (bool-val
   (bool boolean?))

  ; variables
  (name-val
   (name symbol?))

  (string-val
   (str string?)))
  

(define num-val?
  (lambda (val)
    (cases expval val
      (num-val (num) #t)
      (else #f))))

(define string-val?
  (lambda (val)
    (cases expval val
      (string-val (str) #t)
      (else #f))))

(define bool-val?
  (lambda (val)
    (cases expval val
      (bool-val (bool) #t)
      (else #f))))

;; expval extraction functions
(define expval->str
  (lambda (val)
    (cases expval val
      (string-val (str) str)
      (else (report-expval-extractor-error 'str val)))))
    
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))

(define expval->name
  (lambda (val)
    (cases expval val
      (name-val (name) name)
      (else (report-expval-extractor-error 'name val)))))

(define report-expval-extractor-error
  (lambda (type val)
    (eopl:error 'expval-> "Exp value ~s could not be extracted as type ~s" val type)))


;; ----------------------------------Helper functions ----------------------------------


; value-of-names: Extracts parameter names to map to values later
(define value-of-names
  (lambda (names-exp)
    (cases names names-exp
      (names-list (name name-prime)
        (cons name (value-of-name-prime name-prime)))
      
      (epsilon-names ()
                     '()))))

; value-of-name-prime: Is called on the rest of names passed from above.
(define value-of-name-prime
  (lambda (name-prime-exp)
    (cases name-prime name-prime-exp
      (names-list-prime (name name-prime)
        (cons name (value-of-name-prime name-prime)))
      (epsilon-name-prime ()
        '()))))

; value-of-arguments: Computes expressions passed in as arguments by calling value-of with each expr
(define value-of-arguments
  (lambda (arg-list)
    (cases argument-expressions arg-list
      (argument-list (expr arg-list-prime)
        (cons (value-of expr) (value-of-arguments-prime arg-list-prime)))

      (epsilon-argument-expressions ()
                                    '()))))

; value-of-arguments-prime: Does the same thing but on the rest of the list, recursive function.
(define value-of-arguments-prime
  (lambda (arg-list-prime)
    (cases argument-expressions-prime arg-list-prime
      (argument-list-prime (expr arg-list-prime-next)
        (cons (value-of expr) (value-of-arguments-prime arg-list-prime-next)))
      (epsilon-argument-list ()
        '()))))

; Apply-closure function:
; The apply closure functions works by extracting the closure structure values (params, body, env)

(define apply-closure
  (lambda (c1 args)
    (cases closure c1
      (a-closure (params body closure-env)
                 
        ; Arugments match?
        (unless (= (length params) (length args))
          (eopl:error 'apply-closure "Argument count mismatch"))
        
        ; New environement as copy of old one
        (let ((new-env (hash-copy closure-env)))
          
          ; Bind parameters to arguments in the new environment
          (for-each (lambda (param arg)
                      (hash-set! new-env param (wrap-value arg))) ; Wrap the value here before extending to env
                    params
                    args)
          
          ; Save the old environment and set the global environment to the new one
          (let ((old-env global-env))
            (set! global-env new-env)
            
            ; Evaluate the function body
            (let ((result (value-of-block body)))
              
              ;; Restore the global environment
              (set! global-env old-env)
              
              ; Check if a return value was produced
              (if (return-value? result)
                  (return-value-value result) ;; Extract and return the value
                  (if (equal? result 'undefined)
                      'undefined ;; Return 'undefined' if no value
                      result)))))))))


; Wrap-value: Takes a raw value, wraps into an expval object.
(define wrap-value
  (lambda (val)
    (cond
      [(number? val) (num-val val)]
      [(boolean? val) (bool-val val)]
      [(string? val) (string-val val)]
      [else val])))


;; ---------------------------------- Core Interpreter ----------------------------------
;; This section contains all the value functions that compute each of the different grammar rules
;; its not ordered to match the grammar -- note
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (statements)
        (value-of-statements-top statements)))))

(define value-of-statements-top
  (lambda (stmts)
    (let loop ((stmts stmts) (results '()))
      (cases statements stmts
        (statements-list (stmt rest)
          (let ((result (value-of-statement stmt)))
            (loop rest
                  (if (or (equal? result 'done)
                          (equal? result 'undefined))
                      results
                      (cons result results)))))
        (epsilon-statements ()
          (reverse results))))))


; value-of-statements loops through each individual statement.
; if a return statement is encountered, the result is returned immediately.
(define value-of-statements
  (lambda (stmts)
    (let loop ((stmts stmts))
      (cases statements stmts
        (statements-list (stmt rest)
          (let ((result (value-of-statement stmt)))
            (if (return-value? result)
                result ;; Propagate return value immediately
                (loop rest))))
        (epsilon-statements ()
          'undefined)))))


; value-of-statement assesses what type of statement is currently being executed.
(define value-of-statement
  (lambda (stmt)
    (cases statement stmt

      ; Return statement
      (return-stmt (exp)
        (let ((value (value-of exp)))
          (a-return-value value))) ; Construct a return-value instance

      ; Constant declaration
      (const-stmt (name exp)
                  (let ((value (value-of exp)))
                    (cond
                      [(number? value)
                       (extend-env name (num-val value))]
                       
                      [(string? value)
                       (extend-env name (string-val value))]
                       
                      [(boolean? value)
                       (extend-env name (bool-val value))]
                      )
                       
                    'done))
      
      ; Function declaration
      ; Functions need to: 1) create the closure 2) store it in the env
      (function-decl-stmt (name params block)
        (let* ((param-names (value-of-names params))
               (closure (make-closure param-names block global-env)))
          (extend-env name closure)
          'done))
                     
      ; basic expression
      (expr-stmt (exp)
        (value-of exp))

      ; if-statements
      (if-statement-stmt (if-stmt)
                         (value-of-if-statement if-stmt))
      )))


; value-of: only has one case as expression is defined as term expression-prime.
(define value-of
  (lambda (exp)
    (cases expression exp
      
      ;; Handle expression
      (expr (term exp-prime)
        (let ((term-val (value-of-term term)))
          (value-of-expression-prime exp-prime term-val))))))

; expression-prime: Responsible for logical operations, addition, subraction and ternary operations.
(define value-of-expression-prime
  (lambda (exp-prime left-val)
    (cases expression-prime exp-prime

      ;; Addition and subtraction
      (add-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (+ left-val right-val))))
      
      (sub-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (- left-val right-val))))

      ;; Comparison operators
      ; >
      (gt-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (if (> left-val right-val) #t #f))))

      ; <
      (lt-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (if (< left-val right-val) #t #f))))

      ; >=
      (gte-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (if (>= left-val right-val) #t #f))))

      ; <=
      (lte-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (if (<= left-val right-val) #t #f))))

      ; ===
      (eql-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (if (equal? left-val right-val) #t #f))))

      ; !==
      (not-eql-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (if (not (equal? left-val right-val)) #t #f))))

      ;; Ternary operations
      (ternary-exp (true-exp false-exp)
        (let ((cond-value left-val))
          (if cond-value
              (value-of true-exp)
              (value-of false-exp))))

      ;; Logical OR
      (or-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (or left-val right-val))))

      ;; Logical AND
      (and-exp (term exp-prime)
        (let ((right-val (value-of-term term)))
          (value-of-expression-prime exp-prime (and left-val right-val))))

      (epsilon-expr-prime ()
        left-val))))


; value-of-term: similar to value-of. Extracts the first term via value-of-factor, then calls term-prime
(define value-of-term
  (lambda (term-exp)
    (cases term term-exp
      (trm (factor term-prime)
        (let ((factor-val (value-of-factor factor)))
          (value-of-term-prime term-prime factor-val))))))

; value-of-term-prime: Computes multiplication, division, and modulo.
; mult,div,mod are here so they can be computed first as the order of operations dictates.
(define value-of-term-prime
  (lambda (term-prime-exp left-val)
    (cases term-prime term-prime-exp

      ; *
      (mult-exp (factor term-prime)
        (let ((right-val (value-of-factor factor)))
          (value-of-term-prime term-prime (* left-val right-val))))

      ; /
      (div-exp (factor term-prime)
        (let ((right-val (value-of-factor factor)))
          (if (zero? right-val)
              (eopl:error "Division by zero")
              (value-of-term-prime term-prime (/ left-val right-val)))))

      ; %
      (mod-exp (factor term-prime)
               (let ((right-val (value-of-factor factor)))
                 (if (zero? right-val)
                     (eopl:error 'value-of-term-prime "Modulo by zero")
                     (value-of-term-prime term-prime (modulo left-val right-val)))))

       (epsilon-term-prime ()
        left-val))))


; value-of-if-statements: evaluates condition (cond-exp) then either evaluates the block
; or calls value-of-else-branch.
(define value-of-if-statement
  (lambda (if-stmt-bs)
    
    ;; Cases deconstructs the if-statement
    (cases if-statement if-stmt-bs
      (if-stmt (cond-exp then-block else-branch)

        ;; Evaluate the condition expression
        (let ((cond-value (value-of cond-exp)))
         
          ;; Check the boolean value of the condition
          (if cond-value
              (value-of-block then-block)
              (value-of-else-branch else-branch)))))))

               
; value-of-else-branch: Has two options, evaluate block of look at next if statement
(define value-of-else-branch
  (lambda (else-branch-bs)
    (cases else-branch else-branch-bs
      (else-block (block)
                  (value-of-block block))

      (else-if-stmt (stmt)
                    (value-of-if-statement stmt))

    )))

; Value of block: Blocks are statements so just evaluate all statements in the block
(define value-of-block
  (lambda (block-passed)
    (cases block block-passed
      (block-stmt (stmts)

                  (value-of-statements stmts)))))
                  

; Value-of-factor: VoF will return the RAW value.
; For constants, raw values are extracted using the expval functions.
(define value-of-factor
  (lambda (factor-exp)
    (cases factor factor-exp
      (const-exp (num)
         num)

       ; Handle name-or-call-factor-exp
      (name-or-call-factor-exp (noc-exp)
        (cases name-or-call noc-exp
          (name-or-call-exp (name call-prime)
            (cases name-or-call-prime call-prime
              
              ; Variable reference
              (epsilon-call-prime ()
                                  
                ; Handle variable reference
                (let ((val (apply-env name)))
                  (if (closure? val)
                      (eopl:error 'value-of-factor "Variable ~s is a function, not a value" name)

                      ; Return the variable's value
                      (cond
                        [(num-val? val) (expval->num val)]
                        [(bool-val? val) (expval->bool val)]
                        [(string-val? val) (expval->str val)]
                        [else val]))))

              ; Function call
              (function-call-exp (arg-list)

                ; Handle function call
                (let ((closure (apply-env name)) ; get function and its args
                      (args (value-of-arguments arg-list))) ; compute args before we apply
                  (if (closure? closure)
                      (apply-closure closure args)
                      (eopl:error 'value-of-factor "Variable ~s is not a function" name))))))))
                               
      ; ( expression )
      (paren-exp (exp)
                 (value-of exp))

      (neg-exp (factor)
               (- (value-of-factor factor)))

      (true-exp () #t)

      (false-exp () #f)

      (string-exp (str)
                  str)

      (not-exp (factor)
               (let ((factor-val (value-of-factor factor)))
                 (if factor-val
                     #f
                     #t)))
      )))


;; REPL and the start of the interpreter.

(define (repl)
  (let loop ()
    
    ;; Read user input
    
    (display "> ") ; Prompt
    
    (let ((input (read-line))) ; Repl only reads one line at a time.
      (if (equal? input "exit")
          (displayln "Exiting Interpreter...") ; Exiting prompt.
          (let ((results (run input)))
            
            ;; Check if results is a list
            (if (list? results)
                
                ;; Iterate over the list of results
                (for-each
                 (lambda (result)
                   (unless (or (equal? result 'done)
                               (equal? result 'undefined))
                     (displayln result)))
                 results)
                
                ;; Handle single result or 'done
                (unless (or (equal? results 'done)
                            (equal? results 'undefined))
                  (displayln results)))
            
            
            (loop))))) ; Recursive call
  )
(repl)