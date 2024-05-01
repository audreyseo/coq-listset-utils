From Coq Require Import List Lists.ListSet.
From ListSetUtils Require Import Basic.



Lemma remove_symmetric :
  forall (T: Type) (Teq_dec: forall (t1 t2: T), {t1 = t2} + {t1 <> t2}) (s: set T) (t1 t2: T),
    set_remove Teq_dec t1 (set_remove Teq_dec t2 s)
    =s set_remove Teq_dec t2 (set_remove Teq_dec t1 s).
Proof.
  induction s; simpl; split; intros; eauto.
  - destruct (Teq_dec t2 a), (Teq_dec t1 a); subst.
    + eauto.
    + simpl. destruct (Teq_dec a a); try congruence.
    + simpl in H. destruct (Teq_dec a a); try congruence.
    + simpl in *. destruct (Teq_dec t1 a), (Teq_dec t2 a); try congruence.
      simpl in *. destruct H; eauto.
      right. eapply IHs; eauto.
  - destruct (Teq_dec t1 a), (Teq_dec t2 a); subst; eauto; simpl in *; try destruct (Teq_dec a a); subst; try congruence.
    destruct (Teq_dec t1 a), (Teq_dec t2 a); try congruence.
    simpl in *. destruct H; eauto. right. eapply IHs. eauto.
Qed.

Lemma in_and_not_in_neq :
  forall (T: Type) (Teq_dec : forall (t1 t2: T), {t1 = t2} + {t1 <> t2})
    (s: set T) (t t0: T),
    In t s ->
    ~ In t0 s ->
    t <> t0.
Proof.
  induction s; simpl; intros; eauto.
  destruct H.
  + subst. intros Not. destruct H0. eauto.
  + intros Not. subst. destruct H0. eauto.
Qed.


Lemma remove_involutive :
  forall (T: Type) Teq_dec (s: set T) (t t0: T),
    NoDup s ->
    In t
       (set_remove Teq_dec t0
                   (set_remove Teq_dec t0 s)) <->
      In t (set_remove Teq_dec t0 s).
Proof.
  induction s; simpl; split; intros; try easy; destruct (Teq_dec t0 a).
  + subst. invs H. eapply set_remove_iff in H0; eauto.
      destruct H0. eauto.
  + simpl.  simpl in H0. destruct (Teq_dec t0 a); try congruence.
      simpl in H0. destruct H0; eauto.
      invs H.
      eapply IHs in H0; eauto.
  + subst. invs H. eapply set_remove_iff; eauto.
    assert (t <> a). eapply in_and_not_in_neq; eauto.
    split; eauto.
  + invs H. simpl in H0. destruct H0.
    * subst. simpl. destruct (Teq_dec t0 t).
      -- subst. contradiction.
      -- simpl. eauto.
    * eapply set_remove_iff in H0; eauto.
      destruct H0.
      simpl. destruct (Teq_dec t0 a); try congruence.
      simpl. right. eapply IHs; eauto. eapply set_remove_iff; eauto.
Qed.
