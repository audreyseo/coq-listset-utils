From Coq Require Import List Lists.ListSet.
From ListSetUtils Require Import Basic Utils.

Ltac destruct_set_union :=
  match goal with
  | [ |- ~ In ?x (set_union _ _ _)] =>
      eapply not_in_sets_not_in_set_union
  | [ |- context G [In ?x (set_union _ _ _)]] =>
      erewrite set_union_iff
  | [ H: ~ In ?x (set_union _ _ _) |- _ ] =>
      eapply not_in_set_union in H;
      let In1 := fresh "Hin1" in
      let In2 := fresh "Hin2" in
      destruct H as (In1 & In2)
  | [ H: context G [In ?x (set_union _ _ _)] |- _] =>
      erewrite set_union_iff in H
  end.
