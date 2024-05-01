From Coq Require Import List Lists.ListSet.
From ListSetUtils Require Import Tactics Basic.

Section SetBinaryOps.
  Hypothesis (A T: Type).
  Hypothesis (Teq_dec: forall (t1 t2: T), {t1 = t2} + {t1 <> t2}).
  Hypothesis (l: list A).
  Hypothesis (f: A -> set T).
  Hypothesis (init: set T).
  Hypothesis (Initnodup: NoDup init).
  Hypothesis (Fnodup: forall (a: A), NoDup (f a)).

  Section SetUnion.
    Let fold_func := (fun (v: A) (acc: set T) =>
                        set_union Teq_dec acc (f v)).

    Lemma in_fold_right_union_iff :
      forall (t: T),
        In t (fold_right fold_func init l) <->
          In t (fold_right fold_func nil l) \/
            In t init.
    Proof using fold_func Teq_dec l f init.
      unfold fold_func.
      clear Initnodup. clear Fnodup. revert init.
      induction l; simpl; intros; split; intros Pre; eauto.
      - destruct Pre; try easy.
      - erewrite set_union_iff in *. destruct Pre.
        + eapply IHl0 in H. destruct H; eauto.
        + eauto.
      - erewrite set_union_iff in *. erewrite IHl0 in Pre. erewrite IHl0. destruct Pre; eauto.
        destruct H; eauto.
        destruct H; try easy. eauto.
    Qed.

    Lemma in_fold_in_fold_right_union :
      forall (t: T),
        In t (fold_right fold_func nil l) ->
        In t (fold_right fold_func init l).
    Proof using fold_func Teq_dec l f init.
      intros. eapply in_fold_right_union_iff; eauto.
    Qed.

    Lemma in_init_in_fold_right_union :
      forall (t: T),
        In t init ->
        In t (fold_right fold_func init l).
    Proof using fold_func Teq_dec l f init.
      intros. eapply in_fold_right_union_iff; eauto.
    Qed.

    Lemma not_in_sets_not_in_fold_right_union :
      forall (t: T),
        ~ In t (fold_right fold_func nil l) ->
        ~ In t init ->
        ~ In t (fold_right fold_func init l).
    Proof using fold_func Teq_dec l f init.
      intros. erewrite in_fold_right_union_iff. intros Not.
      destruct Not; try easy.
    Qed.

    Lemma not_in_fold_right_union :
      forall (t: T),
        ~ In t (fold_right fold_func init l) ->
        ~ In t (fold_right fold_func nil l) /\ ~ In t init.
    Proof using fold_func Teq_dec l f init.
      intros. erewrite in_fold_right_union_iff in H. split; intros Not; destruct H; eauto.
    Qed.
  End SetUnion.

  Section SetDiff.
    Let fold_func := (fun (v: A) (acc: set T) =>
                        set_diff Teq_dec acc (f v)).
    Lemma in_fold_right_diff_iff :
      forall (t: T),
        In t (fold_right fold_func init l) <->
          In t init
          /\
            ~ In t (fold_right (fun (v: A) (acc: set T) =>
                                  set_union Teq_dec acc (f v))
                               nil l).
    Proof using Type*.
      unfold fold_func. clear Fnodup. clear Initnodup. revert init. induction l; simpl; split; intros; eauto.
      - destruct H. eauto.
      - eapply set_diff_iff in H. destruct H. eapply IHl0 in H. destruct H.
        split; eauto. eapply Utils.not_in_sets_not_in_set_union; eauto.
      - destruct H. eapply set_diff_iff. eapply Utils.not_in_set_union in H0.
        destruct H0. split; eauto.
        eapply IHl0; split; eauto.
    Qed.

    Lemma in_fold_right_diff_backward :
      forall (t: T),
        In t init ->
        ~ In t (fold_right (fun (v: A) (acc: set T) =>
                              set_union Teq_dec acc (f v))
                           nil l) ->
        In t (fold_right fold_func init l).
    Proof using Type*.
      intros. eapply in_fold_right_diff_iff. split; eauto.
    Qed.

    Lemma in_fold_right_diff_forward :
      forall (t: T),
        In t (fold_right fold_func init l) ->
          In t init
          /\
            ~ In t (fold_right (fun (v: A) (acc: set T) =>
                                  set_union Teq_dec acc (f v))
                               nil l).
    Proof using Type*.
      intros. eapply in_fold_right_diff_iff in H. eauto.
    Qed.

    Lemma not_in_fold_right_diff_forward :
      forall (t: T),
        ~ In t (fold_right fold_func init l) ->
        ~ In t init
        \/
          In t (fold_right (fun (v: A) (acc: set T) =>
                              set_union Teq_dec acc (f v))
                           nil l).
    Proof using Type*.
      intros. erewrite in_fold_right_diff_iff in H.
      eapply Decidable.not_and in H.
      - destruct H; eauto.
        eapply Decidable.not_not in H; eauto.
        unfold Decidable.decidable.
        destruct (set_In_dec Teq_dec t (fold_right (fun (v: A) (acc: set T) =>
                                              set_union Teq_dec acc (f v))
                                                   nil l)); eauto.
      - unfold Decidable.decidable. destruct (set_In_dec Teq_dec t init); eauto.
    Qed.

    Lemma not_in_fold_right_diff_backward1 :
      forall (t: T),
        ~ In t init ->
        ~ In t (fold_right fold_func init l).
    Proof using Type*.
      intros. erewrite in_fold_right_diff_iff. intros Not. destruct Not. easy.
    Qed.

    Lemma not_in_fold_right_diff_backward2 :
      forall (t: T),
        In t (fold_right (fun (v: A) (acc: set T) => set_union Teq_dec acc (f v)) nil l) ->
        ~ In t (fold_right fold_func init l).
    Proof using Type*.
      intros. erewrite in_fold_right_diff_iff. intros Not.
      destruct Not. easy.
    Qed.
  End SetDiff.

  Section SetInter.
    Let fold_func := (fun (v: A) (acc: set T) =>
                        set_inter Teq_dec acc (f v)).

    Lemma in_fold_right_inter_iff :
      forall (t: T),
        In t (fold_right fold_func init l) <->
          (Forall (fun (v: A) => In t (f v)) l)
          /\ In t init.
    Proof using Type*.
      unfold fold_func. clear Initnodup. clear Fnodup. revert init.
      induction l; simpl; intros; split; intros Pre; try destruct Pre; eauto.
      - eapply set_inter_iff in Pre. destruct Pre.
        eapply IHl0 in H. destruct H. split; eauto.
      - eapply set_inter_iff. invc H.
        split; eauto.
        eapply IHl0; eauto.
    Qed.

    Lemma in_fold_right_inter_intro :
      forall (t: T),
        Forall (fun (v: A) => In t (f v)) l ->
        In t init ->
        In t (fold_right fold_func init l).
    Proof using Type*.
      intros. eapply in_fold_right_inter_iff; split; eauto.
    Qed.

    Lemma in_fold_right_inter_elim :
      forall (t: T),
        In t (fold_right fold_func init l) ->
        (Forall (fun (v: A) => In t (f v)) l) /\ In t init.
    Proof using Type*.
      intros. eapply in_fold_right_inter_iff in H. eauto.
    Qed.

    Lemma not_in_fold_right_inter :
      forall (t: T),
        ~ In t (fold_right fold_func init l) ->
        Exists (fun (v: A) => ~ In t (f v)) l
        \/ ~ In t init.
    Proof using Type*.
      intros. erewrite in_fold_right_inter_iff in H.
      eapply Decidable.not_and in H.
      - destruct H.
        + eapply neg_Forall_Exists_neg in H; eauto. intros.
          eapply (set_In_dec Teq_dec t (f x)).
        + right. eauto.
      - unfold Decidable.decidable.
        pose proof (Forall_Exists_dec (fun v : A => In t (f v))).
        simpl in X. assert (forall x: A,
                               {In t (f x)} + {~ In t (f x)}).
        { intros x. eapply (set_In_dec Teq_dec t (f x)). }
        specialize (X X0).
        specialize (X l). destruct X; eauto.
        eapply Exists_Forall_neg in e; eauto.
        intros x. pose proof (set_In_dec Teq_dec t (f x)).
        destruct H1; eauto.
    Qed.

    Lemma not_in_fold_right_intro1 :
      forall (t: T),
        ~ In t init ->
        ~ In t (fold_right fold_func init l).
    Proof using Type*.
      intros. erewrite in_fold_right_inter_iff. intros Not. destruct Not. easy.
    Qed.

    Lemma not_in_fold_right_intro2 :
      forall (t: T),
        ~ Forall (fun x: A => In t (f x)) l ->
        ~ In t (fold_right fold_func init l).
    Proof using Type*.
      intros. erewrite in_fold_right_inter_iff. intros Not. destruct Not. easy.
    Qed.

    Lemma not_in_fold_right_intro2' :
      forall (t: T),
        Exists (fun x : A => ~ In t (f x)) l ->
        ~ In t (fold_right fold_func init l).
    Proof using Type*.
      intros. eapply Exists_Forall_neg in H. eapply not_in_fold_right_intro2. eauto.
      intros. pose proof(set_In_dec Teq_dec t (f x)).
      destruct H1; eauto.
    Qed.
      
              
                                                            
      
      
    
        
      
    
    
      
      
    
      
     
End SetBinaryOps.
    
      
      
        

    

    
    
