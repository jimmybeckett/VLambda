Require Import String.
Require Import Bool.
Require Import Logic.
Add LoadPath "~/cse/VLambda".
Load eval.

(* Exact (not alpha!) equality *)
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

Definition divergence (expr : Expr) : Prop:= 
exists (n : nat), equalExpr expr (take_n_steps expr (S n)) = true.

Theorem divergence_example : divergence ((L "a" | (($"a") ($"a"))) (L "a" | (($"a") ($"a")))).
Proof.
exists 0. reflexivity. Qed.