Require Import String.

Inductive Expr : Type :=
  | Var (name : string)
  | Combination (expr1 : Expr) (expr2 : Expr)
  | Abstraction (bound : string) (body : Expr).

Definition betaReduce (expr : Expr) (old : string) (new : Expr) : Expr :=
  let fix substitute (expr : Expr) : Expr :=
      match expr with
      | Var v => if eqb v old then new else expr
      | Combination expr1 expr2 => Combination (substitute expr1) (substitute expr2)
      | Abstraction bound body => if eqb bound old 
                                  then expr 
                                  else Abstraction bound (substitute body)
      end
  in substitute expr.

(* Returns Some expr' if a step is taken, and None if no step is possible *)
Fixpoint step (expr : Expr) : option Expr :=
  match expr with
  | Combination (Abstraction bound body) arg => Some (betaReduce body bound arg)
  | Combination e1 e2 => match step e1 with
                          | Some e1' => Some (Combination e1' e2)
                          | None => match step e2 with
                                    | Some e2' => Some (Combination e1 e2')
                                    | None => None
                                    end
                          end
  | Abstraction bound body => match step body with
                              | Some body' => Some (Abstraction bound body')
                              | None => None
                              end
  | Var _ => None
  end.

Fixpoint take_n_steps (expr : Expr) (n : nat) : Expr :=
  match step expr, n with
  | Some expr', S n' => take_n_steps expr' n'
  | _, _ => expr
  end.

(* Evaluate using small-step semantics *)
Definition eval_step (expr : Expr) : Expr := take_n_steps expr 4096.

(* Lambda calculus big-step semantics *)
Fixpoint eval_depth (expr : Expr) (maxDepth : nat) : option Expr :=
  match expr, maxDepth with
  | Combination e1 e2, S maxDepth' => 
    let e1' := eval_depth e1 maxDepth' in
    let e2' := eval_depth e2 maxDepth' in
      match e1', e2' with
      | Some (Abstraction bound body), Some arg  => eval_depth (betaReduce body bound arg) maxDepth'
      | Some e1'', Some e2'' => Some (Combination e1'' e2'')
      | _, _ => None
      end
  | Abstraction bound body, S maxDepth' => 
    match eval_depth body maxDepth' with 
    | None => None 
    | Some body' => Some (Abstraction bound body')
    end
  | Var _, S _ => Some expr
  | _, O => None (* max recursion depth reached *)
  end.

Definition eval (expr : Expr) : option Expr :=
  eval_depth expr 4096 (* arbitrarily chosen max recursion depth *).

(* Exact (not alpha!) equality. Simplifies a reasonable amount before comparing. *)
Definition equalExpr (expr1 : Expr) (expr2 : Expr) : bool :=
  let fix equalExprSimp (expr1 : Expr) (expr2 : Expr) : bool :=
    match expr1, expr2 with
      | Combination e1 e2, Combination e1' e2' => andb (equalExprSimp e1 e1') (equalExprSimp e2 e2')
      | Abstraction bound body, Abstraction bound' body' => 
        andb (eqb bound bound') (equalExprSimp body body')
      | Var v, Var v' => eqb v v'
      | _, _ => false
    end in
  equalExprSimp (eval_step expr1) (eval_step expr2).

(* Will write real parser later, this will do for now *)
(* lambda x.lambda y.xy ==> L "x" | L "y" | (($"x") ($"y")) *)
Notation "'L' x | y" := (Abstraction x y) (at level 70, right associativity).
Notation "( x ) ( y )" := (Combination x y) (at level 80).
Notation "$ x" := (Var x) (at level 90).

(* A simple example, using booleans *)
(* Definitions all use different variables to avoid breaking scuffed beta reduction *)
Definition T := L "a" | L "b" | $"a".
Definition F := L "c" | L "d" | $"d". 
Definition and :=  L "x" | L "y" | ((($"x") ($"y")) (F)).

Compute eval (((and) (T)) (T)). (* T *)
Compute eval (((and) (T)) (F)). (* F *)
Compute eval (((and) (F)) (T)). (* F *)
Compute eval (((and) (F)) (F)). (* F *)

Fixpoint prettyPrint (expr : Expr) : string :=
  match expr with
  | Var s => s
  | Combination e1 e2 => "(" ++ (prettyPrint e1) ++ ")" ++ "(" ++ (prettyPrint e2) ++ ")"
  | Abstraction bound body => "L " ++ bound ++ "." ++ (prettyPrint body) 
  end.

Compute eval ((L "x" | L "z" | $"x") ($"y")).

Definition y1 := ($"f") (($"x") ($"x")).
Definition y2 := L "x" | (($"f") (($"x") ($"x"))).

Definition Y := L "f" | L "x" | ((y1) (y2)).

Compute prettyPrint Y.

Compute prettyPrint (match eval ((Y) ($"g")) with Some e' => e' | None => $"jeepus creepus" end).



Definition e0 := (Y) ($"g").
Compute prettyPrint e0.

Definition e1 := match step e0 with Some e' => e' | None => $"jeepus creepus" end.
Compute prettyPrint e1.
Definition e2 := match step e1 with Some e' => e' | None => $"jeepus creepus" end.
Compute prettyPrint e2.

Compute prettyPrint (match e with Some e' => e' | None => $"x" end).













