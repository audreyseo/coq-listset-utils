From Coq Require Import List Lists.ListSet.

From ListSetUtils Require Import Basic Utils Tactics FoldRight.

Section SetBinaryOps.
  Hypothesis (A T: Type).
  Hypothesis (Teq_dec: forall (t1 t2: T), {t1 = t2} + {t1 <> t2}).
  Hypothesis (l: list A).
  Hypothesis (f: A -> set T).
  Hypothesis (init: set T).
  Hypothesis (Initnodup: NoDup init).
  Hypothesis (Fnodup: forall (a: A), NoDup (f a)).

  Let left_func set_fun: set T -> A -> set T :=
        (fun (acc: set T) (v: A) =>
           set_fun Teq_dec acc (f v)).

  Let right_func set_fun : A -> set T -> set T :=
        (fun (v: A) (acc: set T) =>
           set_fun Teq_dec acc (f v)).

  Lemma fold_left_right_union :
    fold_left (left_func (@set_union T)) l init
    =s fold_right (right_func (@set_union T)) init l.
  Proof using left_func right_func Teq_dec l f init.
    unfold left_func, right_func.
    clear Fnodup. clear Initnodup. revert init.
    induction l; simpl; split; intros; eauto.
    - eapply set_union_iff. eapply in_fold_left_iff in H. destruct H.
      + left. eapply IHl0; eauto. eapply in_fold_left_iff. left. eauto.
      + destruct_set_union. destruct H.
        * left. eapply IHl0; eauto. eapply in_fold_left_iff. eauto.
        * eauto.
    - eapply IHl0; eauto using set_union_nodup.
      eapply set_union_iff in H. destruct H.
      + eapply in_fold_right_union_iff.
        eapply in_fold_right_union_iff in H. destruct H; eauto.
        right. destruct_set_union; eauto.
      + eapply in_fold_right_union_iff. right. eapply set_union_iff.
        eauto.
  Qed.

  Lemma fold_left_right_diff :
    fold_left (left_func (@set_diff T)) l init
    =s fold_right (right_func (@set_diff T)) init l.
  Proof using left_func right_func Teq_dec l f init.
    unfold left_func, right_func.
    clear Fnodup. clear Initnodup. revert init.
    induction l; simpl; split; intros; eauto.
    - eapply set_diff_iff. eapply IHl0 in H. 
    

  
  
                      

  
              
             
