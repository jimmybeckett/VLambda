Require Import String.
Require Import Bool.
Require Import Logic.
Add LoadPath "~/cse/VLambda".
Load eval.

Definition divergence (expr : Expr) : Prop:= 
exists (n : nat), equalExpr expr (take_n_steps expr (S n)) = true.

Theorem divergence_example : divergence ((L "a" | (($"a") ($"a"))) (L "a" | (($"a") ($"a")))).
Proof.
exists 0. reflexivity. Qed.
