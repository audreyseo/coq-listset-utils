From Coq Require Import List Lists.ListSet.
Print LoadPath.
From ListSetUtils Require Import Basic.

Section FoldLeftPreservesNoDup.
  Hypothesis (A T: Type).
  Hypothesis (Teq_dec: forall (t1 t2: T), {t1 = t2} + {t1 <> t2}).
  Hypothesis (l: list A).
  Hypothesis (f: A -> set T).

  Lemma fold_left_union_nodup :
    forall (init: set T)
      (Fnodup: forall (a: A), NoDup (f a)),
      NoDup init ->
      NoDup
        (fold_left
           (fun (acc : set T) (y : A) =>
              set_union Teq_dec acc (f y)) l
           init).
  Proof using Teq_dec l f.
    induction l; intros.
    - simpl. assumption.
    - simpl. eapply IHl0; eauto. eapply set_union_nodup; eauto.
  Qed.

  Lemma fold_left_add_nodup :
    forall (f: A -> T),
    forall (init: set T),
      NoDup init ->
      NoDup (fold_left
               (fun (acc: set T) (y: A) =>
                  set_add Teq_dec (f y) acc)
               l
               init).
  Proof using Teq_dec l.
    induction l; simpl; intros; eauto.
    - simpl. eapply IHl0. eapply set_add_nodup. eauto.
  Qed.

  Lemma fold_left_remove_nodup :
    forall (f: A -> T),
    forall (init: set T),
      NoDup init ->
      NoDup (fold_left
               (fun (acc: set T) (y: A) =>
                  set_remove Teq_dec (f y) acc)
               l
               init).
  Proof using Teq_dec l.
    induction l; simpl; intros; eauto.
    eapply IHl0. eapply set_remove_nodup; eauto.
  Qed.

  Lemma fold_left_diff_nodup :
    forall (init: set T)
      (Fnodup: forall (a: A), NoDup (f a)),
      NoDup init ->
      NoDup (fold_left
               (fun (acc: set T) (y: A) =>
                  set_diff Teq_dec acc (f y))
               l
               init).
  Proof using Teq_dec l f.
    induction l; simpl; intros; eauto using set_diff_nodup.
  Qed.


  Lemma fold_left_inter_nodup :
    forall (init: set T)
      (Fnodup: forall (a: A), NoDup (f a)),
      NoDup init ->
      NoDup (fold_left
               (fun (acc: set T) (y: A) =>
                  set_inter Teq_dec acc (f y))
               l
               init).
  Proof using Teq_dec l f.
    induction l; simpl; intros; eauto using set_inter_nodup.
  Qed.
End FoldLeftPreservesNoDup.
             
