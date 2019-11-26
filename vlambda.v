Require Import String.
Require Import List.
Import ListNotations.
Require Import Datatypes.
Require Import Nat.

(* See http://homepage.cs.uiowa.edu/~slonnegr/plf/Book/Chapter5.pdf *)

Inductive Expr : Type :=
| Var (name : string)
| Combination (expr1 : Expr) (expr2 : Expr)
| Abstraction (bound : string) (body : Expr).

Notation "'L' x | y" := (Abstraction x y) (at level 70, right associativity).
Notation "( x ) ( y )" := (Combination x y) (at level 80, right associativity).
Notation "$ x" := (Var x) (at level 90, right associativity).

(* Scuffed beta reduction, does not correctly distinguish between bound and free variables *)
Definition betaReduce (expr : Expr) (old : string) (new : Expr) : Expr :=
let fix substitute (expr : Expr) : Expr :=
    match expr with
    | Var v => if String.eqb v old then new else expr
    | Combination expr1 expr2 => Combination (substitute expr1) (substitute expr2)
    | Abstraction bound body => Abstraction bound (substitute body)
    end
in substitute expr.

Definition eval (expr : Expr) : option Expr :=
let fix evalOpt (expr : Expr) (n : nat) : option Expr :=
  match expr, n with
  | Combination e1 e2, S n' => 
    let e1' := evalOpt e1 n' in
    let e2' := evalOpt e2 n' in
      match e1', e2' with
      | Some (Abstraction bound body), Some arg  => evalOpt (betaReduce body bound arg) n'
      | Some e1'', Some e2'' => Some (Combination e1'' e2'')
      | _, _ => None
      end
  | Abstraction bound body, S n' => 
    match evalOpt body n' with 
    | None => None 
    | Some v => Some (Abstraction bound v)
    end
  | Var s, _ => Some expr
  | _, O => None (* recursion limit reached *)
  end
in evalOpt expr 1024.


Definition T := L "a" | L "b" | $"a".
Definition F := L "a" | L "b" | $"b".

Definition and :=  L "x" | L "y" | ((($"x") ($"y")) (F)).

Compute eval (((and) (T)) (T)). (* T *)
Compute eval (((and) (T)) (F)). (* F *)
Compute eval (((and) (F)) (T)). (* F *)
Compute eval (((and) (F)) (F)). (* F *)






