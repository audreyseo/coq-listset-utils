From Coq Require Import String List.
Local Open Scope string_scope.

Eval compute in ("hi").

Ltac invs H := inversion H; subst.

Ltac invc H := invs H; clear H.


(* Set equality *)
Global Infix "=s" := (fun s1 s2 => forall x, In x s1 <-> In x s2) (at level 70).
