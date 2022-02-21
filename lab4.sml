(***********************************************************)
(*       LISP interpreter                                  *)
(*                                                         *)
(*       Ashby Glover                                      *)
(*       Lab 4 COMP 360                                    *)
(*                                                         *)
(***********************************************************)

exception EvalError of string;
exception LexerError;
exception ParseOK;
exception ParseError of string;
exception UnboundVar;
exception ParameterMismatch;

(***********************************************************)
(* type declarations                                       *)
(***********************************************************)

datatype sign =
   Plus
 | Minus;

datatype atom =
   T
 | NIL
 | Int of int
 | Ident of string;

datatype token =
   Lparen
 | Rparen
 | Dot
 | Sign of sign
 | Atom of atom;

datatype sexp =
   AtomExp of atom
 | Sexp of sexp * sexp;

let
    (***********************************************************)
    (* globals                                                 *)
    (***********************************************************)
    val lineno = ref 1;
    val dlist = ref (AtomExp(NIL));

    (***********************************************************)
    (* printing functions                                      *)
    (***********************************************************)

    (* function: print_tokens - prints out a token stream  *)
    fun print_tokens [] = print("\n")
      | print_tokens (Lparen :: t) = (print("Lparen "); print_tokens(t))
      | print_tokens (Rparen :: t) = (print("Rparen "); print_tokens(t))
      | print_tokens (Dot :: t) = (print("Dot "); print_tokens(t))
      | print_tokens (Sign(Plus) :: t) = (print("Plus "); print_tokens(t))
      | print_tokens (Sign(Minus) :: t) = (print("Minus "); print_tokens(t))
      | print_tokens (Atom(a) :: t) =
      (case a of
             T => (print("Atom(T) "); print_tokens(t))
           | NIL => (print("Atom(NIL) "); print_tokens(t))
           | Int i => (print("Atom(Int(" ^ Int.toString(i) ^ ")) "); print_tokens(t))
           | Ident s => (print("Atom(Ident(" ^ s ^ ")) "); print_tokens(t)));

    (* function: string_of_op -  converts an operator token to a string *)
    fun string_of_op Plus = "+"
     |  string_of_op Minus = "-";


    (* function: is_list - predicate function returning true if s-expression is a list *)
    fun is_list (Sexp(h, AtomExp(NIL))) = true
     |  is_list (Sexp(h, t)) = is_list t
     |  is_list _ = false;


    (* function: string_of_atom - converts a primitive atom to a string *)
    fun string_of_atom (T) = "t"
     |  string_of_atom (NIL) = "nil"
     |  string_of_atom (Int(i)) = Int.toString i
     |  string_of_atom (Ident(i)) = i;

    (* function: string_of_token - converts a lexer token to a string *)
    fun string_of_token (Lparen) = "("
     |  string_of_token (Rparen) = ")"
     |  string_of_token (Dot) = "."
     |  string_of_token (Sign(s)) = string_of_op s
     |  string_of_token (Atom(a)) = string_of_atom a;

    (* function: print_list - prints an s-expression in list format *)
    fun print_list (AtomExp(NIL)) = ()
     |  print_list (AtomExp(a)) = print(string_of_atom a)
     |  print_list (Sexp(h,AtomExp(NIL))) = print_sexp h
     |  print_list (Sexp(h,t)) =
           (print_sexp h;
            print " ";
            print_list t)

    (* function: print_sexp - prints an s-expression in either dotted or list format *)
    and print_sexp s =
      if (is_list s) then
         (print "(";
         print_list s;
         print ")")
      else
        (case s of
              AtomExp(a) => print (string_of_atom a)
            | Sexp(h,t) =>
                (print "(";
                print_sexp h;
                print " . ";
                print_sexp t;
                print ")"));


    (***********************************************************)
    (* lexer implementation                                    *)
    (***********************************************************)

    (* function: spaces - eats whitespace between tokens *)
    fun spaces (#" " :: t)  = spaces t
      | spaces (#"\t" :: t) = spaces t
      | spaces (#"\n" :: t) = (lineno := !lineno + 1; spaces t)
      | spaces l = l;

    (* function: char_to_int - converts character to integer with error checking *)
    fun char_to_int(c) =
      let
        val copt = Int.fromString(Char.toString(c))
      in
        (case copt of
              SOME(vv) => vv
            | NONE => raise LexerError)
      end;


    (* function: lexid - assembles characters into an Ident token *)
    fun lexid (s, []) = (s, [])
      | lexid (s, h::t) =
      if Char.isAlphaNum(h) then
        lexid(s ^ Char.toString(h), t)
      else
        (s, h::t);

    (* function: lexint - assembles digits into an Int token *)
    fun lexint (v, []) = (v, [])
      | lexint (v, h::t) =
      if Char.isDigit(h) then
        lexint((10*v)+char_to_int(h), t)
      else
        (v, h::t);

    (* function: lexer - main tokenizer driver; maps character stream to token stream *)
    fun  lexer( #"(" :: t) =   Lparen :: lexer(t)
      |  lexer( #")" :: t) =  Rparen :: lexer(t)
      |  lexer( #"." :: t) =  Dot :: lexer(t)
      |  lexer( #"-" :: t) =  Sign(Minus) :: lexer(t)
      |  lexer( #"+" :: t) =  Sign(Plus) :: lexer(t)
      |  lexer( h::t ) =
             if Char.isAlpha(h) then
               let
                 val (idstr,tt) = lexid(Char.toString(h), t)
               in
                 (case (String.map Char.toLower idstr) of
                       "nil" => Atom(NIL) :: lexer(tt)
                     | "t"   => Atom(T) :: lexer(tt)
                     | _     => Atom(Ident(idstr)) :: lexer(tt))
               end
             else if Char.isDigit(h) then
               let
                 val (intval, tt) = lexint(char_to_int(h), t)
               in
                 Atom(Int(intval)) :: lexer(tt)
               end
             else if (h = #"\n") then
               (lineno := !lineno + 1; lexer(spaces(t)))
                  else if Char.isSpace(h) then
                    lexer(spaces(t))
                  else
                    (print ("ERROR: Illegal character on line " ^ Int.toString(!lineno) ^ ": " ^ Char.toString(h));
                              raise LexerError)
      |   lexer [] = [];


    (***********************************************************)
    (* parser implementation                                   *)
    (***********************************************************)

    (* function: check_sign - both validates and combines sign and integer token pairs *)
    fun check_sign (Sign(Minus)::(Atom(Int(i)))::rest) = (AtomExp(Int(~i)),rest)
     |  check_sign (Sign(Plus)::(Atom(Int(i)))::rest) = (AtomExp(Int(i)),rest)
     |  check_sign _ = raise ParseError "+/- sign may only be used with integer literals";


    (* function: parse_sexp - top-level parser: takes stream of tokens, returns sexp-tree *)
    (* S ::= E *)
    fun parse_sexp [] = raise ParseOK
     |  parse_sexp exp = parse_exp exp

    (* E ::= atom | '(' X          *)
    and parse_exp (Lparen::rest) = parse_x rest
     |  parse_exp (Sign(s)::rest) = check_sign (Sign(s)::rest)
     |  parse_exp (Atom(a)::rest) = (AtomExp(a), rest)
     |  parse_exp _ = raise ParseError "parse ended expecting '(' or an atom expression"

    (* X ::= E Y | ')'   *)
    and parse_x (Rparen::rest) = (AtomExp(NIL),rest)
     |  parse_x sexp =
        let
          val (e,rest1) = parse_exp sexp
          val (y,rest2) = parse_y   rest1
        in
          (Sexp(e,y), rest2)
         end

    (* Y ::= '.' E ')' | R ')'    *)
    and parse_y (Dot::rest) =
        let
          val (e, rest1) = parse_exp rest
          val rest2 = parse_rparen rest1
        in
          (e,rest2)
        end
      |  parse_y sexp =
         let
           val (r, rest1) = parse_r sexp
           val rest2 = parse_rparen rest1
        in
          (r,rest2)
        end

    (* R ::= E R | empty  *)
    and parse_r (Lparen::rest) =
        let
          val (e,rest1) = parse_exp (Lparen::rest)
          val (r,rest2) = parse_r   rest1
         in
           (Sexp(e,r), rest2)
         end
      |  parse_r (Sign(s)::rest) =
         let
           val (e,rest1) = parse_exp (Sign(s)::rest)
           val (r,rest2) = parse_r   rest1
         in
           (Sexp(e,r), rest2)
         end
     | parse_r (Atom(a)::rest) =
       let
         val (e,rest1) = parse_exp (Atom(a)::rest)
         val (r,rest2) = parse_r   rest1
       in
         (Sexp(e,r), rest2)
       end
     | parse_r rest = (AtomExp(NIL),rest)

    (* convenience production for right parens *)
    and parse_rparen (Rparen::rest) = rest
     |  parse_rparen rest = raise ParseError "parser ended expecting ')'";



    (*****************************************)
    (* interpretation functions              *)
    (*****************************************)

    (* function: bound - checks that referenced variables are bound in a-list *)
    fun bound x z = 
      (case z of
            (*if you find variable, return true, else continue searching through
            * list*)
            Sexp(Sexp(AtomExp(Ident(car)),_), rest) =>
            if x = car then true else bound x rest
            (*if you reach the end of the list without finding variable, return
            * false*)
          | AtomExp(NIL) => false
          | _ => raise EvalError "unsupported parameters to bound")
    ;

    (* function: getval - returns the value of a variable from the a-list.
    * Expects that variable is bound in list*)
    fun getval name alist =
      (case alist of 
            (*search for variable name*)
            Sexp(Sexp(AtomExp(Ident(car)), value), rest) => 
            (*if you find the variable, return the value*)
            if name = car  
            then  
              value 
            (*else continue searching through list*)
            else 
              getval name rest
          | _ => raise EvalError "alist not in correct format")
    ;

    (* function: check_formal - checks function parameters from matching T or NIL *)
    fun check_formal x =
      (case x of 
          (*formal parameters should not be T or NIL*)
          (*check each variable in list, return false if T or NIL and true if
          * the end of the list is reached*)
            Sexp(AtomExp(T),_) => false
          | Sexp(AtomExp(NIL),_) => false
          | Sexp(_, AtomExp(NIL)) => true
          | Sexp(_, rest) => check_formal rest
          | _ => raise EvalError "unsupported parameters to check_formal" )
    ;

    (* function: eval_defun - checks defun usage and adds function def to the global d-list *)
    fun eval_defun s a d =
      (*s should contain function name, formals, and body*)
      (case s of 
            Sexp(AtomExp(Ident(name)), Sexp(formals, Sexp(body, AtomExp(NIL)))) =>
            (case name of 
                (*if function name is cond, defun, or quote, raise error*)
                  "cond" => raise EvalError "COND cannot be redefined"
                | "defun" => raise EvalError "DEFUN cannot be redefined"
                | "quote" => raise EvalError "QUOTE cannot be redefined"
                (*else, check that formals do not contain T or NIl*)
                | _ => if (check_formal formals) 
                       then
                         (*add function def to global d-list*)
                         (d := Sexp(Sexp(AtomExp(Ident(name)), Sexp(formals,
                         body)), !d); AtomExp(Ident(name)))
                       else
                         raise EvalError "Functions may not use formal parameters named T or NIL, and all formal parameters must be unique")
          | _ => raise EvalError "defun must pass in a function name, formals, and body")
    ;


    (* function: addpairs - checks function parameters and binds formals to actuals *)
    fun addpairs xlist ylist z =
      (case xlist of 
            (*if formals reaches end of list, so should actuals, otherwise
            * error*)
            Sexp(AtomExp(NIL), rest) =>
            (case ylist of
                  AtomExp(NIL) => z (*return original a list from function call*)
                | Sexp(_,_) => raise ParameterMismatch
                | _ => raise UnboundVar)
           (*if formals not at end of list, continue building new a-list*)
          | Sexp(xcar, xcdr) =>
              (case ylist of 
                    Sexp(ycar, ycdr) =>
                    let
                      val newz = addpairs xcdr ycdr z
                    in
                      Sexp(Sexp(xcar, ycar), newz)
                    end
                  | AtomExp(NIL) => raise ParameterMismatch
                  | _ => raise UnboundVar)
          | _ => raise EvalError "formals not structured correctly")
    ;

    (* function: eval - top-level s-expression evaluation loop *)
      (* if atoms T or NIL, evaluate to T or NIL respectively. *)
    fun eval (AtomExp(T)) a d = AtomExp(T)
      | eval (AtomExp(NIL)) a d = AtomExp(NIL)

      (* if integer atom, evaluate to itself *)
      | eval (AtomExp(Int(i))) a d = AtomExp(Int(i))

      (* Identifiers match to first matching binding in the a-list *)
      | eval (Sexp(AtomExp(Ident(id)), rest)) a d = 
        (case id of

      (* if first atom is ident quote, no evaluation done *)
              "quote" => 
                (case rest of
                      Sexp(h, AtomExp(NIL)) => h
                    | _ => raise EvalError "quote only takes one parameter")
      
      (* if first atom is the ident "cond," call evcon() *)
            | "cond" =>
                (case rest of
                      Sexp(h, AtomExp(NIL)) => evcon h a d
                    | _ => raise EvalError "cond called incorrectly")
      

      (* if first atom is the ident "defun," call evdefun() *)
            | "defun" => 
                (case rest of 
                      Sexp(h, AtomExp(NIL)) => eval_defun h a d
                    | _ => raise EvalError "defun called incorrectly")
 
           | _ =>
                (case (bound id a) of 
                    true => getval id a
                  | false => raise UnboundVar))

      (* default case, evaluate parameters with evlist *)
      | eval (Sexp(h, t)) a d = 
        let 
          val tail = evlist t a d
        in 
          apply h tail a d
        end
      
      | eval _ _ _ = raise EvalError "eval called incorrectly"


    (* function: evcon - evaluates a COND statement *)
    and evcon x a d =
        (case x of
              Sexp(Sexp(b, Sexp(e, AtomExp(NIL))), rest) =>
              (case (eval b a d) of
                    AtomExp(T) => eval e a d
                  | AtomExp(NIL) => evcon rest a d
                  | _ => raise EvalError "call to eval did not return T or NIL")
            | AtomExp(NIL) => raise EvalError "all conditions eval to NIL"
            | _ => raise EvalError "incorrect evcon parameter x format")



    (* function: evlist - evaluates a list of expressions and returns a list of results *)
    and evlist x a d =
    (case x of
          Sexp(h, rest) => Sexp((eval h a d), (evlist rest a d))
        | AtomExp(NIL) => AtomExp(NIL)
        | _ => raise EvalError "parameter to evlist in incorrect format")
           
    (* function: apply - performs function application, handles built-ins *)
    and apply f x a d =
    (case f of 
        (*car returns the car of the list*)
          (AtomExp(Ident("car"))) =>
          (case x of 
                Sexp(Sexp(car,_), AtomExp(NIL)) => car
              | _ => raise EvalError "CAR requires a single list as argument")

        (*cdr returns the cdr of the list*)
        | (AtomExp(Ident("cdr"))) =>
          (case x of
                Sexp(Sexp(_, cdr), AtomExp(NIL)) => cdr
              | _ => raise EvalError "CDR requires a single list as argument")
        
        (*cons adds a element to the front of a list*)
        | (AtomExp(Ident("cons"))) =>
          (case x of 
                Sexp(car, Sexp(car2, AtomExp(NIL))) => Sexp(car, car2)
              | _ => raise EvalError "CONS requires atom and s-expression as arg")

        (*atom takes an s-expression and returns T if it is an atom, and NIL if
        * it is a pair or list s-expression*)
        | (AtomExp(Ident("atom"))) =>
          (case x of 
                Sexp(AtomExp(a), AtomExp(NIL)) => AtomExp(T) 
              | Sexp(Sexp(_,_), AtomExp(NIL)) => AtomExp(NIL)
              | _ => raise EvalError "ATOM requires one parameter as arg")

        (*int takes an s-expression and returns T if it is a numeric atom, and
        * NIL if not*)
        | (AtomExp(Ident("int"))) =>
          (case x of
                Sexp(AtomExp(Int(i)), AtomExp(NIL)) => AtomExp(T)
              | Sexp(AtomExp(Ident(a)), AtomExp(NIL)) => AtomExp(NIL)
              | Sexp(Sexp(_,_), AtomExp(NIL)) => AtomExp(NIL)
              | _ => raise EvalError "INT requires one parameter as arg")
              
        (*null takes an s-expression and returns T if the s-expression is the
        * atom NIL, and NIL otherwise*)
        | (AtomExp(Ident("null"))) =>
          (case x of
                Sexp(Sexp(AtomExp(NIL),_), AtomExp(NIL)) => AtomExp(T)
              | Sexp(Sexp(_,_), AtomExp(NIL)) => AtomExp(NIL)
              | _ => raise EvalError "NULL requires a single list as argument")

        (*plus returns the sum of two evaluated s-expressions*)
        | (AtomExp(Ident("plus"))) => 
          (case x of 
                Sexp(AtomExp(Int(i)), Sexp(AtomExp(Int(j)), AtomExp(NIL))) =>
                AtomExp(Int((i + j)))
              | _ => raise EvalError "PLUS requires two integers as argument")

        (*minus returns the difference of two evaluated s-expressions*)
        | (AtomExp(Ident("minus"))) =>
          (case x of
                Sexp(AtomExp(Int(i)), Sexp(AtomExp(Int(j)), AtomExp(NIL))) =>
                AtomExp(Int((i - j)))
              | _ => raise EvalError "MINUS requires two integers as argument")
              
        (*times returns the product of two evaluated s-expressions*)
        | (AtomExp(Ident("times"))) =>
          (case x of 
                Sexp(AtomExp(Int(i)), Sexp(AtomExp(Int(j)), AtomExp(NIL))) =>
                AtomExp(Int((i * j)))
              | _ => raise EvalError "TIMES requires two integers as argument")
              
        (*quotient returns the quotient of two evaluated s-expressions when the
        * first is divided by the second*)
        | (AtomExp(Ident("quotient"))) =>
          (case x of 
                Sexp(AtomExp(Int(i)), Sexp(AtomExp(Int(j)), AtomExp(NIL))) =>
                AtomExp(Int((i div j)))
              | _ => raise EvalError "QUOTIENT requires two integers as arg")
              
        (*remainder returns the remainder of the two evaluated s-expressions
        * when the first is divided by the second*)
        | (AtomExp(Ident("remainder"))) =>
          (case x of 
                Sexp(AtomExp(Int(i)), Sexp(AtomExp(Int(j)), AtomExp(NIL))) => 
                AtomExp(Int((i mod j)))
              | _ => raise EvalError "REMAINDER requires two integers as arg")

        (*less returns T if the first evaluated s-expresion is less than the
        * second, otherwise NIL*)
        | (AtomExp(Ident("less"))) =>
          (case x of 
                Sexp(AtomExp(Int(i)), Sexp(AtomExp(Int(j)), AtomExp(NIL))) =>
                if i < j then AtomExp(T) else AtomExp(NIL)
              | _ => raise EvalError "LESS requires two integers as argument")

        (*greater returns T if the first evaluated s-expression is greater than
        * the second, otherwise NIL*)
        | (AtomExp(Ident("greater"))) =>
          (case x of 
                Sexp(AtomExp(Int(i)), Sexp(AtomExp(Int(j)), AtomExp(NIL))) =>
                if i > j then AtomExp(T) else AtomExp(NIL)
              | _ => raise EvalError "GREATER requires two integers as arg")

        (*eq returns T if both s-expressions are the same exact atom or if both
        * s-expressions represent the same numeric value, otherwise NIL*)
        | (AtomExp(Ident("eq"))) =>
          (case x of 
                Sexp(AtomExp(Int(i)), Sexp(AtomExp(Int(j)), AtomExp(NIL))) =>
                if i = j then AtomExp(T) else AtomExp(NIL)
              | _ => raise EvalError "EQ requires two integers as argument")

        (*for any not built-in function*)
        | (AtomExp(Ident(name))) =>
            (*check if function is bound in d-list*)
            if (bound name (!d)) 
            then
              let
                (*get formals and body of function*)
                val s = getval name (!d)
              in
                (case s of
                      Sexp(f, b) =>
                      let 
                        val formals = f
                        val body = b
                        (*create new a-list with the actuals bound to the
                        * formals*)
                        val newa = addpairs formals x a
                      in 
                        (*evaluate the function*)
                       eval body newa d
                      end
                    | _ => raise EvalError "getval not returning correct format")
              end
            else 
              raise UnboundVar
        | _ => raise EvalError "apply not called correctly" )
;


    (*****************************************)
    (* helper routines                       *)
    (*****************************************)

    fun get_sexp [] = (AtomExp(NIL),[])
     |  get_sexp s = parse_sexp s;

    fun next_sexp [] = OS.Process.exit(OS.Process.success)
      | next_sexp s =
        let
          val (e,rest) = get_sexp s
          val e' = eval e (AtomExp(NIL)) dlist
        in
          (print_sexp e';
          print "\n";
          next_sexp rest
          handle ParseError msg => print ("Parse Error: " ^ msg ^ "\n")
               | EvalError msg =>  print ("Evaluation Error: " ^ msg ^ "\n")
               | ParseOK => OS.Process.exit(OS.Process.success))
     end

    fun reader(copt: char option, is, l) =
      case copt of
           NONE    => (TextIO.closeIn is; l)
         | SOME(c) => reader (TextIO.input1 is, is, (l@[c]));


    (*****************************************)
    val args = CommandLine.arguments()
    val ins = TextIO.openIn(hd(args))
    val (sexp,ts) = get_sexp(lexer(reader(TextIO.input1 ins, ins, [])))
    val se' = (eval sexp (AtomExp(NIL)) dlist)


in
    (*****************************************)
    (* main                                  *)
    (*****************************************)

    print_sexp(se');
    print "\n";
    next_sexp ts
end
handle ParseError msg =>  print ("Parse Error: " ^ msg ^ "\n")
     | EvalError msg =>  print ("Evaluation Error: " ^ msg ^ "\n")
     | ParseOk =>  OS.Process.exit(OS.Process.success);
