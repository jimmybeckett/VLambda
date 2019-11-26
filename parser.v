Require Import String.
Add LoadPath "~/cse/VLambda".
Load eval.

Fixpoint prettyPrint (expr : Expr) : string :=
  match expr with
  | Var s => s
  | Combination e1 e2 => "(" ++ (prettyPrint e1) ++ ")" ++ "(" ++ (prettyPrint e2) ++ ")"
  | Abstraction bound body => "L " ++ bound ++ "." ++ (prettyPrint body) 
  end.

Compute prettyPrint ((L "a" | L "b" | (($"a")($"b"))) ($"z")).

