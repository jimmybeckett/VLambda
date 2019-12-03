Require Import String.
Require Import Bool.
Require Import Logic.
Add LoadPath "~/cse/VLambda".
Load eval.

(* Exact (not alpha!) equality. Compares WITHOUT evaluating. Very scuffed *)
Fixpoint equalExpr (expr1 : Expr) (expr2 : Expr) : bool :=
  match expr1, expr2 with
    | Combination e1 e2, Combination e1' e2' => andb (equalExpr e1 e1') (equalExpr e2 e2')
    | Abstraction bound body, Abstraction bound' body' => 
      andb (eqb bound bound') (equalExpr body body')
    | Var v, Var v' => eqb v v'
    | _, _ => false
  end.

Definition divergence (expr : Expr) : Prop:= 
exists (n : nat), equalExpr expr (take_n_steps expr (S n)) = true.

Theorem divergence_example : divergence ((L "a" | (($"a") ($"a"))) (L "a" | (($"a") ($"a")))).
Proof.
exists 0. reflexivity. Qed.