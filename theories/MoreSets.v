From Coq Require Import List Lists.ListSet Arith Psatz.

From ListSetUtils Require Import Basic Utils.



Section MoreSets.
  Hypothesis (A: Type).
  Hypothesis (Aeq_dec: forall (a1 a2: A), { a1 = a2 } + { a1 <> a2 }).
  Section AndMoreSets.
    Hypothesis (s1: set A).
    Lemma set_add_length :
      forall (a: A),
        Datatypes.length s1 <= Datatypes.length (set_add Aeq_dec a s1).
    Proof using A Aeq_dec s1.
      induction s1; intros; simpl.
      - lia.
      - destruct (Aeq_dec a0 a); subst.
        simpl. lia.
        simpl. eapply le_n_S. eauto.
    Qed.

    Lemma set_add_length' :
      forall (a: A),
        { Datatypes.length (set_add Aeq_dec a s1) = S (Datatypes.length s1)} + {Datatypes.length (set_add Aeq_dec a s1) = Datatypes.length s1}.
    Proof using Aeq_dec s1.
      induction s1; intros.
      - simpl. left. reflexivity.
      - simpl. destruct (Aeq_dec a0 a); subst; simpl.
        + right. reflexivity.
        + specialize (IHs a0). destruct IHs.
          * rewrite e. left. reflexivity.
          * rewrite e. right. reflexivity.
    Qed.

    Lemma set_add_add_length :
      forall (a1 a2: A),
        Datatypes.length (set_add Aeq_dec a1 (set_add Aeq_dec a2 s1)) = Datatypes.length (set_add Aeq_dec a2 (set_add Aeq_dec a1 s1)).
    Proof.
    Admitted.

    Lemma set_add_length_in :
      forall (a: A),
      Datatypes.length
         (set_add Aeq_dec a s1) =
        Datatypes.length s1 ->
      set_In a s1.
    Proof using Aeq_dec s1.
      induction s1; intros.
      simpl in H. congruence.
      simpl in H. simpl. destruct (Aeq_dec a0 a); eauto.
    Qed.

    Lemma in_length_set_add :
      forall (a : A),
        set_In a s1 ->
        Datatypes.length (set_add Aeq_dec a s1) = Datatypes.length s1.
    Proof using Aeq_dec s1.
      induction s1; simpl; intros.
      - contradiction.
      - destruct H; subst.
        + destruct (Aeq_dec a0 a0); try congruence.
          simpl. reflexivity.
        + destruct (Aeq_dec a0 a); try congruence; simpl; eauto.
    Qed.

    Lemma set_add_length_not_in :
      forall (a: A),
        Datatypes.length (set_add Aeq_dec a s1) =
          S (Datatypes.length s1) ->
        ~ set_In a s1.
    Proof using Aeq_dec s1.
      induction s1; intros.
      intros NOT. invs NOT.
      simpl. simpl in *. destruct (Aeq_dec a0 a); subst.
      + simpl in H. invs H. eapply n_Sn in H1. contradiction.
      + simpl in H. invs H. eapply IHs in H1. intros NOT.
        destruct NOT; try congruence.
    Qed.

    Lemma not_in_length_set_add :
      forall (a: A),
        ~ set_In a s1 ->
        Datatypes.length (set_add Aeq_dec a s1) = S (Datatypes.length s1).
    Proof using Aeq_dec s1.
      induction s1; intros.
      - simpl. reflexivity.
      - simpl. simpl in H. destruct (Aeq_dec a0 a).
        + unneg H. left. congruence.
        + simpl. destruct (set_In_dec Aeq_dec a0 s).
          * unneg H. eauto.
          * eauto.
    Qed.
    Local Open Scope list_scope.
    Lemma set_add_concat :
      forall (a: A),
        ~ In a s1 ->
        set_add Aeq_dec a s1 = s1 ++ a :: nil.
    Proof using Aeq_dec s1.
      induction s1; intros.
      - reflexivity.
      - simpl. destruct (Aeq_dec a0 a).
        unneg H. left. eauto.
        f_equal. eapply IHs. intros NOT. unneg H. right. eauto.
    Qed.
      

  End AndMoreSets.

  Section EvenMoreSets.
    Hypothesis (s1: set A).

    Lemma set_union_nil_length :
      NoDup s1 ->
      Datatypes.length (set_union Aeq_dec nil s1) = Datatypes.length s1.
    Proof using Aeq_dec s1.
      induction s1; intros; simpl; eauto.
      invs H. eapply IHs in H3.
      assert (~ set_In a (set_union Aeq_dec nil s)).
      intros NOT. eapply set_union_iff in NOT. destruct NOT. invs H0. contradiction.
      eapply not_in_length_set_add in H0. rewrite H0. eauto.
    Qed.

    Local Open Scope list_scope.


    Eval compute in (set_union Nat.eq_dec (0 :: 1 :: 2 :: 3 :: nil) (4 :: 5 :: 6 :: 7 :: nil)).
    
    Lemma set_union_singleton :
      forall (a: A),
        NoDup s1 ->
        ~ In a s1 ->
        set_union Aeq_dec (a :: nil) s1 = (a :: nil) ++ (rev s1).
    Proof using Aeq_dec s1.
      induction s1; intros.
      - simpl. reflexivity.
      - simpl. invs H. eapply IHs in H3; eauto.
        assert (~ In a0 s).
        intros NOT. unneg H0. simpl. right. eauto.
        eapply IHs in H1; eauto. rewrite H1.
        erewrite <- IHs; eauto.
        rewrite H1. simpl. destruct (Aeq_dec a a0).
        unneg H0. left. eauto. rewrite set_add_concat; eauto.
        erewrite in_rev. erewrite rev_involutive. invs H. eauto.
        intros NOT. unneg H0. right. eauto.
    Qed.
        
    
      
  End EvenMoreSets.
  Local Open Scope list_scope.

  Eval compute in (set_union Nat.eq_dec (1 :: nil) (2 :: 1 :: 3 :: nil)).
  Lemma set_union_singleton_in :
    forall (s1: set A) (a: A),
      NoDup s1 ->
      In a s1 ->
      set_union Aeq_dec (a :: nil) s1 = a :: rev (set_remove Aeq_dec a s1).
  Proof using Aeq_dec.
    induction s1; intros.
    - invs H0.
    - simpl in H0. destruct H0.
      + subst. simpl.
        invs H. erewrite set_union_singleton; eauto.
        simpl. destruct (Aeq_dec a0 a0); try congruence.
      + simpl. destruct (Aeq_dec a0 a). subst. invs H. contradiction.
        invs H. erewrite IHs1; eauto.
        simpl. destruct (Aeq_dec a a0); try congruence.
        f_equal. erewrite set_add_concat. reflexivity.
        unfold not. intros. eapply in_rev in H1.
        eapply set_remove_iff in H1; eauto.
        destruct H1. contradiction.
  Qed.

  Lemma set_remove_length :
    forall (s1: set A) (a: A),
      In a s1 ->
      S (Datatypes.length (set_remove Aeq_dec a s1)) = Datatypes.length s1.
  Proof using Aeq_dec.
    induction s1; intros.
    - simpl. invs H.
    - simpl in H. simpl. destruct (Aeq_dec a0 a); try congruence.
      destruct H; try congruence.
      eapply IHs1 in H. simpl. rewrite H. reflexivity.
  Qed.
    
        
      
    
  Section AndAndMoreSets.
    Hypothesis (s1: set A).
    Lemma set_union_cons :
      forall (s2: set A) (a: A)
        (NODUP: NoDup s2)
        (NODUP': NoDup (a :: s1)),
        Datatypes.length (set_union Aeq_dec (a :: s1) s2) = Datatypes.length (set_union Aeq_dec s1 (a :: s2)).
    Proof using Aeq_dec s1.
      induction s1; intros.
      - simpl. destruct s2. simpl. reflexivity.
        simpl. destruct (set_add_length' (set_union Aeq_dec (a :: nil) s2) a0).
        + rewrite e. destruct (set_add_length' (set_add Aeq_dec a0 (set_union Aeq_dec nil s2)) a).
          * rewrite e0. f_equal.
            destruct (set_add_length' (set_union Aeq_dec nil s2) a0).
            -- rewrite e1.  invs NODUP.
               erewrite set_union_nil_length; eauto.
               eapply set_add_length_not_in in e0.
               erewrite set_add_iff in e0. erewrite set_union_iff in e0.
               assert (~ In a s2).
               intros NOT. unneg e0. right. eauto.
               rewrite set_union_singleton; eauto.
               simpl. rewrite rev_length. reflexivity.
            -- eapply set_add_length_not_in in e0.
               assert (~ set_In a s2).
               intros NOT. unneg e0. eapply set_add_iff. right. eapply set_union_iff. right. eauto.
               eapply set_add_length_not_in in e.
               eapply set_add_length_in in e1.
               eapply set_union_iff in e1. destruct e1.
               invs H0.
               invs NODUP. contradiction.
          * rewrite e0. eapply set_add_length_in in e0.
            pose proof (P := e0).
            eapply set_add_iff in e0. destruct e0.
            -- subst.
               erewrite in_length_set_add in e. eapply n_Sn in e. contradiction.
               eapply set_union_iff. left. left. eauto.
            -- destruct (Aeq_dec a a0).
               ++ subst. erewrite in_length_set_add in e. eapply n_Sn in e. contradiction.
                  eapply set_union_iff. left. left. eauto.
               ++ invs NODUP. rewrite not_in_length_set_add.
                  f_equal. rewrite set_union_singleton_in; eauto.
                  simpl. erewrite rev_length. erewrite set_remove_length.
                  erewrite set_union_nil_length. reflexivity.
                  eauto. eapply set_union_iff in H. destruct H.
                  invs H. eauto.
                  eapply set_union_iff in H. destruct H; eauto. invs H.
                  intros NOT. eapply set_union_iff in NOT; destruct NOT; simpl in *; try congruence.
                  
        + eapply set_add_length_in in e. invs NODUP.
          eapply set_union_iff in e. destruct e; try contradiction.
          simpl in H. destruct H; try contradiction.
          subst.
          rewrite in_length_set_add. rewrite set_union_singleton.
          simpl. rewrite in_length_set_add. rewrite not_in_length_set_add. rewrite set_union_nil_length. rewrite rev_length. reflexivity.
          eauto.
          intros NOT. eapply set_union_iff in NOT. simpl in NOT. destruct NOT; contradiction.
          eapply set_add_iff. eauto.
          eauto. eauto.
          eapply set_union_iff. simpl. eauto.
      - simpl.
        revert NODUP. induction s2; intros.
        + simpl. destruct (Aeq_dec a0 a). invs NODUP'. simpl in H1. unneg H1. left. reflexivity.
          simpl. invs NODUP'.
          assert (~ In a0 s).
          intros NOT. unneg H1. right. eauto.
          rewrite not_in_length_set_add. reflexivity. eauto.
        + simpl. invs NODUP. eapply IHs2 in H2.
          destruct (set_In_dec Aeq_dec a0 (set_add Aeq_dec a1 (set_union Aeq_dec (a :: s) s2))).
          * symmetry. rewrite in_length_set_add. symmetry.
            destruct (set_In_dec Aeq_dec a1 (set_union Aeq_dec (a :: s) s2)).
            -- erewrite in_length_set_add; eauto.
               eapply set_add_iff in s0. destruct s0; subst.
               ++ eapply set_union_iff in s3. destruct s3.
                  ** invs NODUP'. contradiction.
                  ** contradiction.
               ++ eapply set_union_iff in H. destruct H.
                  invs NODUP'. contradiction.
                  rewrite in_length_set_add in H2.
                  rewrite H2. rewrite in_length_set_add. reflexivity.
                  eapply set_union_iff. left. eapply set_union_iff in s3.
                  destruct s3; try contradiction. eauto.
                  eapply set_union_iff. right. eauto.
               ++ eapply set_union_iff. eapply set_union_iff in s3.
                  destruct s3; try congruence.
                  left. right. eauto.
            -- symmetry. erewrite not_in_length_set_add; eauto. symmetry.
               destruct (Aeq_dec a0 a1).
               ++ subst. rewrite in_length_set_add. rewrite H2.
                  rewrite not_in_length_set_add.  reflexivity. eauto.
                  eapply set_union_iff. left. left. reflexivity.
               ++ eapply set_add_iff in s0. destruct s0; try congruence.
                  assert (~ set_In a1 (set_union Aeq_dec (a0 :: a :: s) s2)).
                  unfold not. intros. eapply set_union_iff in H0. destruct H0; try contradiction.
                  unneg n.
                  eapply set_union_iff. left. simpl in H0. destruct H0; try congruence. eauto.
                  rewrite not_in_length_set_add. invs NODUP. erewrite IHs2. erewrite in_length_set_add. reflexivity.
                  eauto. eauto.
                  eauto.
            -- eauto.
          * symmetry. erewrite not_in_length_set_add; eauto.
            symmetry.
            destruct (set_In_dec Aeq_dec a1 (set_union Aeq_dec (a0 :: a :: s) s2)).
            -- rewrite in_length_set_add; eauto.
               erewrite set_add_iff in n.
               assert (a0 <> a1) by (intros NOT; unneg n; left; eauto).
               invs NODUP. erewrite IHs2; eauto.
               assert (~ In a0 (set_union Aeq_dec (a :: s) s2)) by (intros NOT; unneg n; eauto).
               rewrite not_in_length_set_add; eauto.
               eapply set_union_iff in s0. destruct s0; try contradiction.
               simpl in H3. destruct H3; try congruence.
               destruct H3.
               ++ subst. erewrite in_length_set_add. reflexivity. eapply set_union_iff. left. left. eauto.
               ++ erewrite IHs; eauto.
                  simpl. destruct (set_In_dec Aeq_dec a (set_union Aeq_dec s s2)).
                  ** erewrite in_length_set_add; eauto.
                     erewrite in_length_set_add. erewrite IHs; eauto. simpl. erewrite in_length_set_add. reflexivity.
                     eauto. invs NODUP'. eauto.
                     eapply set_union_iff. left. right. eauto.
                  ** erewrite not_in_length_set_add; eauto.
                     erewrite in_length_set_add; eauto.
                     erewrite IHs; eauto. simpl. erewrite not_in_length_set_add; eauto.
                     invs NODUP'. eauto. eapply set_union_iff. left. simpl. eauto.
                  ** invs NODUP'. eauto.
            -- erewrite not_in_length_set_add; eauto.
               erewrite not_in_length_set_add; eauto.
               erewrite H2. erewrite not_in_length_set_add.
               reflexivity.
               erewrite set_add_iff in n. intros NOT. unneg n. right. eauto.
               intros NOT. eapply set_union_iff in NOT. destruct NOT.
               ++ unneg n0. eapply set_union_iff. left. right. eauto.
               ++ contradiction.
    Qed.

  End AndAndMoreSets.

  Lemma in_set_set_add_noop :
    forall (s: set A) (a: A),
      In a s ->
      set_add Aeq_dec a s = s.
  Proof using Aeq_dec.
    induction s; intros.
    - invs H.
    - simpl in H. destruct H.
      + subst. simpl. destruct (Aeq_dec a0 a0); try congruence.
      + eapply IHs in H. simpl. destruct (Aeq_dec a0 a).
        * subst. reflexivity.
        * rewrite H. reflexivity.
  Qed.

  Lemma set_union_length_comm :
    forall (s1 s2: set A),
      NoDup s1 ->
      NoDup s2 ->
      Datatypes.length (set_union Aeq_dec s1 s2) = Datatypes.length (set_union Aeq_dec s2 s1).
  Proof using Aeq_dec.
    induction s1; intros.
    - rewrite set_union_nil_length; eauto.
    - simpl. invs H.
      destruct (set_In_dec Aeq_dec a s2).
      + erewrite in_length_set_add. rewrite set_union_cons; eauto.
        simpl. erewrite in_length_set_add. eauto.
        eapply set_union_iff. eauto.
        eapply set_union_iff; eauto.
      + rewrite set_union_cons; eauto. simpl. erewrite not_in_length_set_add. erewrite not_in_length_set_add. f_equal; eauto.
        intros NOT. eapply set_union_iff in NOT. destruct NOT; contradiction.
        intros NOT. eapply set_union_iff in NOT. destruct NOT; contradiction.
  Qed.

  Lemma set_union_length_add_in_other :
    forall (s1 s2: set A)
      (a: A)
      (NODUP': NoDup s1)
      (NODUP: NoDup s2),
      In a s2 ->
      Datatypes.length (set_union Aeq_dec (set_add Aeq_dec a s1) s2) =
        Datatypes.length (set_union Aeq_dec s1 s2).
  Proof using Aeq_dec.
    induction s1; intros.
    - simpl. revert H. revert a. induction s2; intros.
      + invs H.
      + simpl in H. destruct H; subst.
        * simpl. erewrite in_length_set_add. erewrite set_union_length_comm. simpl. destruct (set_In_dec Aeq_dec a0 (set_union Aeq_dec nil s2)).
          -- symmetry. erewrite in_length_set_add.
             eapply set_union_iff in s; destruct s.
             invs H.
             erewrite in_length_set_add; eauto. erewrite set_union_nil_length; eauto.
             invs NODUP. eauto.
             eauto.
          -- symmetry. rewrite not_in_length_set_add; eauto.
             symmetry. rewrite not_in_length_set_add; eauto.
             invs NODUP. rewrite set_union_nil_length; eauto.
             unfold not. intros. unneg n. eapply set_union_iff. right. eauto.
          -- econstructor. unfold not; intros. invs H. econstructor.
          -- invs NODUP. eauto.
          -- eapply set_union_iff. left. simpl. eauto.
        * simpl.
          destruct (set_In_dec Aeq_dec a (set_union Aeq_dec nil s2)).
          -- symmetry. rewrite in_length_set_add; eauto.
             erewrite in_length_set_add.
             symmetry. eapply IHs2. invs NODUP. eauto. eauto. eapply set_union_iff. eapply set_union_iff in s. destruct s; try invs H0.
             right. eauto.
          -- destruct (Aeq_dec a a0).
             ++ subst. erewrite set_union_iff in n. unneg n. right. eauto.
             ++ rewrite not_in_length_set_add.
                erewrite not_in_length_set_add.
                f_equal. eapply IHs2; eauto.
                invs NODUP. eauto.
                eauto.
                intros NOT. eapply set_union_iff in NOT. simpl in NOT. destruct NOT; try congruence.
                destruct H0; try congruence; try contradiction.
                unneg n. eapply set_union_iff. right. eauto.
    - invs NODUP'. simpl. destruct (Aeq_dec a0 a); try congruence.
      erewrite set_union_cons; eauto. simpl.
      destruct (set_In_dec Aeq_dec a s2).
      + erewrite in_length_set_add.
        erewrite set_union_cons; eauto.
        simpl. erewrite in_length_set_add.
        erewrite IHs1; eauto.
        all: eapply set_union_iff; eauto.
      + erewrite not_in_length_set_add.
        erewrite set_union_cons; eauto.
        simpl. erewrite not_in_length_set_add. f_equal. eauto.
        all: erewrite set_union_iff; intros NOT.
        destruct NOT; try contradiction.
        destruct NOT; try contradiction.
        eapply set_add_iff in H0. destruct H0; try congruence; try contradiction.
      + econstructor.
        * erewrite set_add_iff. intros NOT. destruct NOT; try congruence.
        * eapply set_add_nodup. eauto.
  Qed.
        
      
             
         
               

  Section MoreMoreSets.
    Hypothesis (s1: set A).
    Lemma set_add_length_union :
      forall (s2: set A) (a: A)
        (NODUP1: NoDup s1)
        (NODUP2: NoDup s2),
        Datatypes.length (set_add Aeq_dec a (set_union Aeq_dec s1 s2)) = Datatypes.length (set_union Aeq_dec (set_add Aeq_dec a s1) s2).
    Proof using A Aeq_dec s1.
      induction s1; simpl; intros.
      - revert a. induction s2; intros. simpl. reflexivity.
        simpl. rewrite set_add_add_length.
        
        pose proof (set_add_length' (set_add Aeq_dec a0 (set_union Aeq_dec nil s2)) a).
        destruct H.
        + rewrite e. pose proof (set_add_length' (set_union Aeq_dec (a0 :: nil) s2) a). destruct H.
          * invs NODUP2. rewrite e0. f_equal.
            eauto.
          * pose proof (set_add_length_in _ _ e0).
            eapply set_union_iff in H.
            erewrite IHs2. rewrite e0.
            pose proof (set_add_length_not_in _ _ e).
            erewrite set_add_iff in H0. simpl in H. erewrite set_union_iff in H0. unneg H0. destruct H.
            -- destruct H; try contradiction. left. congruence.
            -- eauto.
            -- invs NODUP2. eauto.
        + rewrite e. pose proof (set_add_length' (set_union Aeq_dec (a0 :: nil) s2) a). destruct H.
          * rewrite e0. rewrite IHs2.
            eapply set_add_length_in in e. eapply set_add_length_not_in in e0. eapply set_add_iff in e. erewrite set_union_iff in e0.
            unneg e0.
            -- destruct e.
               ++ left. simpl. eauto.
               ++ simpl. right. eapply set_union_iff in H. destruct H; try invs H. eauto.
            -- invs NODUP2. eauto.
          * rewrite e0. invs NODUP2. eauto.
      - revert a0 NODUP1. revert a. revert NODUP2. induction s2; intros.
        + simpl. reflexivity.
        + simpl. invs NODUP2. invs NODUP1. destruct (Aeq_dec a0 a); subst.
          * destruct (set_add_length' (set_union Aeq_dec
                                                 (if Aeq_dec a1 a then a :: s else a :: set_add Aeq_dec a1 s) s2) a).
            -- destruct (Aeq_dec a1 a).
               eapply set_add_length_not_in in e. unneg e. eapply set_union_iff. left. simpl. eauto.
               eapply set_add_length_not_in in e. erewrite set_union_iff in e. unneg e. left. simpl. eauto.
            -- destruct (Aeq_dec a1 a).
               ++ rewrite e. pose proof (set_add_length_in _ _ e).
                  subst. 
                  assert (set_In a (set_add Aeq_dec a (set_add Aeq_dec a (set_union Aeq_dec (a :: s) s2)))) by (eapply set_add_iff; left; reflexivity).
                  erewrite in_length_set_add; eauto.
                  eapply set_add_iff. left. reflexivity.
               ++ rewrite e.
                  destruct (set_add_length' (set_add Aeq_dec a (set_union Aeq_dec (a :: s) s2)) a1).
                  ** rewrite e0. eapply set_add_length_not_in in e0.
                     erewrite IHs2. destruct (Aeq_dec a a); try congruence.
                     erewrite set_union_cons. simpl. erewrite set_union_cons. rewrite <- IHs. simpl.
                     assert (~ set_In a1 (set_add Aeq_dec a (set_union Aeq_dec s s2))).
                     intros NOT. eapply set_add_iff in NOT. destruct NOT; try congruence. erewrite set_add_iff in e0. assert (~In a1 (set_union Aeq_dec (a :: s) s2)).
                     intros NOT. unneg e0. right. eauto.
                     erewrite set_union_iff in H, H0. unneg H0.
                     destruct H; eauto.
                     left. right. eauto.
                     eapply not_in_length_set_add in H. rewrite H. reflexivity. eauto. eauto. eauto. econstructor. erewrite set_add_iff. intros NOT.
                     invs NODUP1. destruct NOT; try congruence.
                     
                     eapply set_add_nodup; eauto.
                     eauto. eauto. eauto. eauto.
                  ** eapply set_add_length_in in e0; eauto.
                     erewrite in_length_set_add; eauto.
                     assert (set_In a (set_union Aeq_dec (a :: s) s2)).
                     eapply set_union_iff. left. left. eauto.
                     erewrite IHs2; eauto. destruct (Aeq_dec a a); try congruence; eauto.
                     eapply set_add_iff in e0.
                     destruct e0; try congruence.
                     eapply set_union_iff in H0. destruct H0.
                     --- clear e1. simpl in H0. destruct H0; try congruence.
                         rewrite in_set_set_add_noop; eauto.
                     --- rewrite set_union_length_comm; eauto. simpl.
                         (* erewrite not_in_length_set_add. *)
                         symmetry. erewrite set_union_length_comm; eauto. simpl.
                         erewrite not_in_length_set_add. erewrite set_union_length_comm; eauto.
                         erewrite set_union_length_add_in_other; eauto.
                         erewrite not_in_length_set_add. erewrite set_union_length_comm; eauto.
                         all: try erewrite set_union_iff.
                         all: try intros NOT.
                         destruct NOT; try congruence.
                         eapply set_add_nodup; eauto.
                         destruct NOT; try congruence.
                         eapply set_add_iff in H5. destruct H5; try congruence.
                         econstructor. intros NOT.
                         eapply set_add_iff in NOT. destruct NOT; try congruence.
                         eapply set_add_nodup; eauto.
          * destruct (Aeq_dec a1 a0); try congruence.
            -- subst. destruct (set_In_dec Aeq_dec a s), (set_In_dec Aeq_dec a0 s2).
               ++ erewrite in_length_set_add. erewrite in_length_set_add. reflexivity.
                  eapply set_union_iff. left. right. eauto.
                  eapply set_add_iff. right. eapply set_union_iff. right. eauto.
               ++ erewrite in_length_set_add.
                  erewrite in_length_set_add.
                  reflexivity.
                  eapply set_union_iff. left. right. eauto.
                  eapply set_add_iff. right. eapply set_union_iff. left. left. eauto.
               ++ erewrite in_length_set_add. reflexivity.
                  eapply set_add_iff. right. eapply set_union_iff. simpl. eauto.
               ++ erewrite in_length_set_add.
                  erewrite not_in_length_set_add; [ | intros NOT].
                  reflexivity.
                  eapply set_union_iff in NOT. destruct NOT; try congruence.
                  simpl in H. destruct H; try congruence.
                  contradiction.
                  eapply set_add_iff. right. eapply set_union_iff. simpl. eauto.
            -- destruct (set_In_dec Aeq_dec a1 (set_union Aeq_dec s s2)), (set_In_dec Aeq_dec a s), (set_In_dec Aeq_dec a0 s2).
               ++ erewrite in_length_set_add. erewrite in_length_set_add.
                  erewrite in_length_set_add.  symmetry. erewrite set_union_cons. simpl. erewrite in_length_set_add.
                  erewrite set_union_cons. simpl. erewrite in_length_set_add.
                  erewrite <- IHs. erewrite in_length_set_add. reflexivity.
                  all: try eapply set_union_iff; simpl; eauto.
                  eapply set_union_iff in s0. destruct s0; eauto.
                  econstructor. unfold not. intros. eapply set_add_iff in H. destruct H; try congruence.
                  eapply set_add_nodup; eauto.
                  left. right. eapply set_add_iff. eauto.
                  eapply set_add_iff. right. eapply set_union_iff in s0. eapply set_union_iff. simpl; destruct s0; eauto.
               ++ rewrite in_length_set_add. rewrite in_length_set_add.
                  rewrite in_length_set_add. symmetry; erewrite set_union_cons; eauto. simpl. erewrite not_in_length_set_add. erewrite <- IHs; eauto. rewrite in_length_set_add; eauto.
                  symmetry; erewrite set_union_length_comm; eauto.
                  simpl. erewrite not_in_length_set_add. erewrite set_union_length_comm; eauto.
                  all: try erewrite set_union_iff; try erewrite set_add_iff; try erewrite set_union_iff; simpl; match goal with
                                                                                                                | [ |- ~ _ ] =>
                                                                                                                    intros NOT

                                                                                                                | [ |- _ ] => idtac
                                                                                                                end; eauto.
                  destruct NOT; try contradiction.
                  destruct NOT; try contradiction. destruct H; try congruence.
                  econstructor. erewrite set_add_iff. intros NOT. destruct NOT; try congruence.
                  eapply set_add_nodup; eauto.
                  left. right. eapply set_add_iff. right. eauto.
                  eapply set_union_iff in s0. destruct s0; eauto.
               ++ erewrite in_length_set_add. erewrite not_in_length_set_add. erewrite not_in_length_set_add. erewrite set_union_length_comm; eauto.
                  symmetry. erewrite set_union_length_comm; eauto.
                  simpl. repeat erewrite in_length_set_add.
                  erewrite set_union_length_comm; eauto.
                  erewrite <- IHs.
                  erewrite in_length_set_add; eauto using set_union_length_comm.
                  all: eauto.
                  all: simpl; try erewrite set_union_iff; try erewrite set_add_iff; try erewrite set_union_iff; simpl; try erewrite set_add_iff; eapply set_union_iff in s0; eauto.
                  eapply set_add_nodup; eauto.
                  econstructor. erewrite set_add_iff. intros NOT.
                  destruct NOT; try congruence.
                  eapply set_add_nodup; eauto.
                  intros NOT.
                  destruct NOT; try congruence.
                  destruct H; try congruence. destruct H; try congruence.
                  subst. destruct s0; try congruence.
                  contradiction.
                  contradiction.
                  intros NOT. destruct NOT; try contradiction.
                  destruct H; try congruence. contradiction.
                  destruct s0; eauto.
               ++ admit.
    Admitted.

  End MoreMoreSets.

  Lemma set_add_union_length_comm :
    forall (s1 s2: set A)
      (a: A)
      (ND1: NoDup s1)
      (ND2: NoDup s2),
      Datatypes.length (set_add Aeq_dec a (set_union Aeq_dec s1 s2)) =
        Datatypes.length (set_add Aeq_dec a (set_union Aeq_dec s2 s1)).
  Proof using Aeq_dec.
  Admitted.

  Lemma set_add_union_length_leq :
    forall (s1 s2: set A)
      (a: A)
      (NODUP': NoDup s1)
      (NODUP: NoDup s2),
      Datatypes.length (set_add Aeq_dec a s2) <= Datatypes.length (set_add Aeq_dec a (set_union Aeq_dec s1 s2)).
  Proof.
    induction s1; intros.
    - destruct (set_In_dec Aeq_dec a s2).
      + erewrite in_length_set_add. erewrite in_length_set_add. erewrite set_union_nil_length. reflexivity.
        eauto. eapply set_union_iff. eauto.
        eauto.
      + erewrite not_in_length_set_add; eauto. erewrite not_in_length_set_add. eapply le_n_S. erewrite set_union_nil_length; eauto.
        intros NOT. eapply set_union_iff in NOT. destruct NOT.
        invs H. contradiction.
    - destruct (set_In_dec Aeq_dec a0 s2).
      + erewrite in_length_set_add; eauto. erewrite in_length_set_add.
        erewrite set_union_length_comm; eauto. simpl. erewrite set_add_union_length_comm; eauto. eapply Nat.le_trans.
        eapply set_add_length.
        eapply IHs1; eauto.
        invs NODUP'. eauto.
        invs NODUP'. eauto.
        eapply set_union_iff. right. eauto.
      + erewrite not_in_length_set_add; eauto.
        destruct (set_In_dec Aeq_dec a0 (a :: s1)).
        * erewrite in_length_set_add.
          erewrite set_union_length_comm; eauto. simpl. erewrite set_add_union_length_comm; eauto. destruct (set_In_dec Aeq_dec a s2).
          -- admit.
  Admitted.
  
        
      

                  
  Lemma set_union_length :
    forall (s1 s2: set A),
    forall (NODUP': NoDup s1),
    forall (NODUP: NoDup s2),
      Datatypes.length s1 <= Datatypes.length (set_union Aeq_dec s1 s2) /\
        Datatypes.length s2 <= Datatypes.length (set_union Aeq_dec s1 s2).
  Proof using A Aeq_dec.
    intros s1 s2. revert s1. induction s2; simpl; intros.
    - split; eauto. lia.
    - split.
      + eapply Nat.le_trans. eapply set_add_length.
        destruct (set_In_dec Aeq_dec a s1).
        * erewrite in_length_set_add. erewrite in_length_set_add. eapply IHs2. eauto. invs NODUP. eauto. eapply set_union_iff. left. eauto.
          eauto.
        * erewrite not_in_length_set_add; eauto.
          destruct (set_In_dec Aeq_dec a s2).
          -- erewrite in_length_set_add. destruct s2; try invs s.
             invs NODUP. unneg H1. eauto.
             invs NODUP. contradiction.
             eapply set_union_iff. right. eauto.
          -- erewrite not_in_length_set_add.
             eapply le_n_S. eapply IHs2; eauto.
             invs NODUP. eauto.
             erewrite set_union_iff. intros NOT. destruct NOT; try contradiction.
      + destruct (set_In_dec Aeq_dec a s1).
        * eapply Nat.le_trans.
          assert (S (Datatypes.length s2) <= Datatypes.length (set_add Aeq_dec a s2)).
          erewrite not_in_length_set_add. reflexivity. invs NODUP. eauto.
          eapply H.
          eapply set_add_union_length_leq; eauto.
          invs NODUP. eauto.
        * rewrite not_in_length_set_add. eapply le_n_S. eapply IHs2; eauto.
          invs NODUP. eauto.
          erewrite set_union_iff. intros N. destruct N; try contradiction.
          invs NODUP. contradiction.
  Qed.

  Lemma set_union_length_each_smaller :
    forall (s1 s2 s3: set A)
      (N1: NoDup s1)
      (N2: NoDup s2),
      Datatypes.length (set_union Aeq_dec s1 s2) <= Datatypes.length s3 ->
      Datatypes.length s1 <= Datatypes.length s3 /\ Datatypes.length s2 <= Datatypes.length s3.
  Proof using Aeq_dec.
    intros. split.
    - eapply Nat.le_trans.
      eapply set_union_length. eapply N2. eauto. erewrite set_union_length_comm; eauto.
    - eapply Nat.le_trans. eapply set_union_length. eapply N1. eauto. eauto.
  Qed.
             
End MoreSets.
