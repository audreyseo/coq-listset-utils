From Coq Require Import Lists.ListSet List String Bool.

From ListSetUtils Require Import Basic.

Local Open Scope list_scope.

Ltac unneg P :=
  let Ptype := type of P in
  (* idtac Ptype; *)
  match Ptype with
  | ~ ?P' => enough P'; try congruence
  | _ => idtac
  end.


Section InSets.
  Hypothesis (T: Type).
  Hypothesis (dec: forall t1 t2: T, {t1 = t2} + {t1 <> t2}).

  Lemma in_set_in_set_add :
    forall (s: set T)
      (x a: T),
      (a = x \/ In x s) <->
      In x (set_add dec a s).
  Proof.
    induction s; intros; split; intros.
    - destruct H; try invs H. simpl. left. eauto.
    - simpl in H. destruct H; try invs H. left. eauto.
    - simpl. destruct (dec a0 a).
      + subst. simpl. destruct H.
        * intuition.
        * simpl in H. assumption.
      + simpl. destruct H.
        * right. eapply IHs. left. eassumption.
        * simpl in H. destruct H.
          -- left. eauto.
          -- right. eapply IHs. right. assumption.
    - simpl in H. destruct (dec a0 a).
      + right. assumption.
      + simpl in H. destruct H.
        * simpl. intuition.
        * simpl. eapply IHs in H. destruct H.
          -- left. eauto.
          -- right. right. eassumption.
  Qed.

  Lemma in_set_in_set_union_nil :
    forall (s: set T)
      (x: T),
      In x s <->
      In x (set_union dec nil s).
  Proof.
    induction s; intros; split; intros.
    - simpl. invs H.
    - simpl in H. invs H.
    - simpl. simpl in H. destruct H.
      + eapply in_set_in_set_add. left. assumption.
      + eapply in_set_in_set_add. right. eapply IHs. eassumption.
    - simpl in H. simpl. eapply in_set_in_set_add in H. destruct H.
      + left. assumption.
      + right. eapply IHs. eassumption.
  Qed.

  Lemma in_set_in_set_union2 :
    forall (s2 s1: set T)
      (x: T),
      In x s2 ->
      In x (set_union dec s1 s2).
  Proof.
    induction s2; intros.
    - invs H. 
    - simpl in H. destruct H.
      + simpl. eapply in_set_in_set_add. left. eauto.
      + simpl. eapply in_set_in_set_add. right. eapply IHs2. eassumption.
  Qed.

  Lemma in_set_in_set_cons :
    forall (s2 s1: set T)
      (x a: T),
      In x (set_union dec (a :: s1) s2) ->
      In x (set_union dec s1 (a :: s2)).
  Proof.
    induction s2; intros.
    - simpl. simpl in H. eapply in_set_in_set_add. eassumption.
    - simpl. simpl in H. eapply in_set_in_set_add in H. eapply in_set_in_set_add. destruct H.
      + right. eapply in_set_in_set_add. left. assumption.
      + eapply IHs2 in H. simpl in H. eapply in_set_in_set_add in H.
        destruct H.
        * left. assumption.
        * right. eapply in_set_in_set_add. right. assumption.
  Qed.

  Lemma in_set_in_set_cons' :
    forall (s2 s1: set T)
      (x a: T),
      In x (set_union dec s1 (a :: s2)) ->
      In x (set_union dec (a :: s1) s2).
  Proof.
    induction s2; intros.
    - simpl. simpl in H. eapply in_set_in_set_add. eassumption.
    - simpl. simpl in H. eapply in_set_in_set_add in H. eapply in_set_in_set_add. destruct H.
      + right. eapply IHs2. simpl. eapply in_set_in_set_add. left. assumption.
      + eapply in_set_in_set_add in H. destruct H.
        * left. assumption.
        * right. eapply IHs2. simpl. eapply in_set_in_set_add. right. assumption.
  Qed.
              
  Lemma in_set_in_set_union_commute :
    forall (s1 s2: set T)
      (x: T),
      In x (set_union dec s1 s2) <->
      In x (set_union dec s2 s1).
  Proof.
    induction s1; intros; split; intros.
    - destruct s2. eassumption.
      simpl in H. simpl. eapply in_set_in_set_add in H. destruct H.
      + left. eassumption.
      + right. eapply in_set_in_set_union_nil. eassumption.
    - simpl in H. eapply in_set_in_set_union_nil in H. eassumption.
    - simpl. eapply in_set_in_set_add.
      destruct s2.
      + simpl in H. destruct H.
        * left. eauto.
        * right. pose proof (in_set_in_set_union_nil).
          specialize (H0 s1 x). destruct H0. eapply H0. eassumption.
      + simpl in H. eapply in_set_in_set_add in H. destruct H.
        * subst. right. eapply IHs1. simpl. eapply in_set_in_set_add. left.
          reflexivity.
        * destruct (dec a x).
          -- left. assumption.
          -- right. destruct (dec t x).
             ++ eapply IHs1. simpl. eapply in_set_in_set_add. left. assumption.
             ++ eapply IHs1. simpl. eapply in_set_in_set_add.
                right. eapply in_set_in_set_cons in H. simpl in H. eapply in_set_in_set_add in H. destruct H; try congruence.
    - simpl in H. eapply in_set_in_set_add in H. destruct H.
      + eapply in_set_in_set_cons'. simpl. eapply in_set_in_set_add. left. eauto.
      + eapply in_set_in_set_cons'. simpl. eapply in_set_in_set_add. right. eapply IHs1. eassumption.
  Qed.
        
             
    
  Lemma in_set_in_set_union1 :
    forall (s1 s2: set T)
      (x: T),
      In x s1 ->
      In x (set_union dec s1 s2).
  Proof.
    induction s1; intros.
    - simpl. invs H.
    - simpl. simpl in H. destruct H.
      + subst. destruct s2.
        * simpl. left. reflexivity.
        * simpl. destruct (dec t x).
          -- eapply in_set_in_set_add. left. eassumption.
          -- eapply in_set_in_set_add. right. eapply in_set_in_set_cons'. simpl.  eapply in_set_in_set_add. left. reflexivity.
      + eapply in_set_in_set_cons'.  simpl. eapply in_set_in_set_add. right. eauto.
  Qed.

  Lemma in_set_union_in_sets :
    forall (s1 s2: set T)
      (x: T),
      In x (set_union dec s1 s2) ->
      In x s1 \/ In x s2.
  Proof.
    induction s1; intros.
    - eapply in_set_in_set_union_nil in H. right. eassumption.
    - eapply in_set_in_set_union_commute in H. simpl in H. eapply in_set_in_set_add in H. simpl. eapply or_assoc. destruct H.
      + left. assumption.
      + right. eapply IHs1. eapply in_set_in_set_union_commute. eassumption.
  Qed.
        

  Lemma not_in_set_union :
    forall (s1 s2: set T)
      (x: T),
      ~ In x (set_union dec s1 s2) ->
      ~ In x s1 /\ ~ In x s2.
  Proof.
    induction s1; intros.
    - split.
      + unfold not; intros. invs H0.
      + pose proof (IN := in_dec dec x s2).
        destruct IN.
        * eapply in_set_in_set_union1 with (s2 := nil) in i. eapply in_set_in_set_union_commute in i. congruence.
        * eauto.
    - enough (~ In x s1 /\ ~ In x s2).
      + assert (x <> a).
        unfold not. intros.
        subst.
        pose proof (in_set_in_set_add (set_union dec s1 s2) a). specialize (H1 a). destruct H1. pose proof (eq_refl a). specialize (H1 (or_introl H3)).
        replace (set_add dec a (set_union dec s1 s2)) with (set_union dec s1 (a :: s2)) in H1 by reflexivity.
        eapply in_set_in_set_cons' in H1. congruence.
        simpl. destruct H0. split.
        * unfold not; intros. destruct H3; try congruence.
        * assumption.
      + eapply IHs1. unfold not. intros.
        assert (In x (set_add dec a (set_union dec s1 s2))).
        eapply in_set_in_set_add. right. assumption.
        replace (set_add dec a (set_union dec s1 s2)) with (set_union dec s1 (a :: s2)) in H1 by reflexivity.
        eapply in_set_in_set_cons' in H1. congruence.
  Qed.

  Lemma not_in_sets_not_in_set_union :
    forall (s1 s2: set T)
      (x: T),
      ~ In x s1 ->
      ~ In x s2 ->
      ~ In x (set_union dec s1 s2).
  Proof.
    induction s1; intros.
    - unfold not. intros. eapply in_set_in_set_union_nil in H1. congruence.
    - unfold not. intros. eapply in_set_in_set_cons in H1. simpl in H1. eapply in_set_in_set_add in H1. destruct H1.
      + assert (In x (a :: s1)).
        {
          simpl. left. assumption.
        }
        congruence.
      + eapply not_in_cons in H. destruct H. revert H1. fold (not (In x (set_union dec s1 s2))). eapply IHs1; eauto.
  Qed.

  Lemma not_in_set_add :
    forall (s: set T)
      (x a: T),
      ~ In x (set_add dec a s) ->
      a <> x /\ ~ In x s.
  Proof.
    induction s; intros.
    - simpl in H. split; unfold not; intros.
      + unneg H. left. assumption.
      + invs H0.
    - simpl in H. destruct (dec a0 a).
      + simpl in H. assert (~ In x (set_add dec a s)).
        unfold not. intros. eapply in_set_in_set_add in H0. congruence.
        eapply IHs in H0. destruct H0. split.
        * subst. assumption.
        * simpl. assumption.
      + simpl in H. assert (~ In x (set_add dec a0 s)).
        unfold not. intros.
        assert (a = x \/ In x (set_add dec a0 s)).
        right. assumption.
        congruence.
        assert (a <> x). unfold not. intros. assert (a = x \/ In x (set_add dec a0 s)). left. assumption. congruence.
        split.
        * unfold not. intros.
          subst. assert (In x (set_add dec x s)).
          eapply set_add_intro2. reflexivity. congruence.
        * unfold not. intros. simpl in H2. destruct H2; try congruence.
          eapply IHs in H0. destruct H0. congruence.
  Qed.

  Lemma fold_left_union_NoDup :
    forall (U: Type) (f: U -> set T) (l: list U) (init: set T),
      (forall (u: U), NoDup (f u)) ->
      NoDup init ->
      NoDup (fold_left (fun acc v =>
                          set_union dec acc (f v))
                       l
                       init).
  Proof.
    induction l; simpl; intros; eauto.
    eapply IHl; eauto.
    eapply set_union_nodup; eauto.
  Qed.

  Lemma not_in_set_remove :
    forall (s: set T) (t t0: T),
      ~ In t (set_remove dec t0 s) ->
      t = t0 \/ (~ In t s).
  Proof using dec.
    induction s; simpl; intros ? ? NotIn.
    - eauto.
    - destruct (dec t0 a).
      + subst. destruct (dec a t).
        * eauto.
        * right. intros NOT. destruct NOT; try congruence.
      + simpl in NotIn.
        eapply Decidable.not_or in NotIn. destruct NotIn. eapply IHs in H0. destruct H0; eauto.
        right. intros Not. destruct Not; try congruence.
  Qed.

  
    
End InSets.

Ltac fold_not :=
  match goal with
  | [ |- ?y -> False ] =>
      fold (~ y)
  end.

Lemma not_in_fold_left_union_not_in_init :
  forall (T U: Type) (Teq_dec: forall (t1 t2: T), { t1 = t2 } + { t1 <> t2 })
    (f: U -> set T) (l: list U) (init: set T) (t: T),
    ~ In t (fold_left (fun acc v => set_union Teq_dec acc (f v))
                      l init) ->
    ~ In t init.
Proof.
  induction l; simpl; intros.
  - eauto.
  - eapply IHl in H. eapply not_in_set_union in H. destruct H. eauto.
Qed.

Lemma not_in_fold_left_union_iff :
  forall (T U: Type) (Teq_dec: forall (t1 t2: T), { t1 = t2 } + { t1 <> t2 })
    (f: U -> set T) (l: list U) (init: set T) (t: T),
    ~ In t (fold_left (fun acc v => set_union Teq_dec acc (f v))
                      l init) <->
    ~ In t (fold_left (fun acc v => set_union Teq_dec acc (f v))
                      l nil) /\
      ~ In t init.
Proof.
  induction l; simpl; split; intros.
  - eauto.
  - destruct H. eauto.
  - split.
    + eapply IHl in H. destruct H. eapply IHl. split; eauto.
      erewrite set_union_iff in *. intros Not.
      destruct Not.
      * invs H1.
      * destruct H0. eauto.
    + eapply IHl in H. destruct H. eapply not_in_set_union in H0. destruct H0. eauto.
  - destruct H. eapply IHl in H. destruct H. eapply not_in_set_union in H1. destruct H1. eapply IHl. split.
    + eauto.
    + eapply not_in_sets_not_in_set_union; eauto.
Qed.
      

Lemma not_in_sets_not_in_fold_left_union :
  forall (T U: Type) (Teq_dec: forall (t1 t2: T), { t1 = t2 } + { t1 <> t2 })
    (f: U -> set T) (l: list U) (init: set T) (t: T),
    ~ In t init ->
    ~ In t (fold_left (fun acc v => set_union Teq_dec acc (f v))
                      l
                      nil) ->
    ~ In t (fold_left (fun acc v => set_union Teq_dec acc (f v))
                      l init).
Proof.
  intros. eapply not_in_fold_left_union_iff.
  split; eauto.
Qed.

(*
Lemma set_add_inter_eq:
forall x s1 s2,
~In x s2 ->
set_inter string_dec (set_add string_dec x s1) s2 = set_inter string_dec s1 s2.
Proof.
  assert (forall x s, In x s -> set_add string_dec x s = s).
  intros.
  induction s. inversion H. simpl. destruct (string_dec x a); eauto.
  f_equal. eapply IHs. simpl in H. destruct H. destruct n; eauto. eauto.
  assert (forall x s, ~In x s -> set_add string_dec x s = List.app s (x::nil)).
  intros. induction s. simpl; eauto. simpl. destruct (string_dec x a). destruct H0.
  simpl; eauto. f_equal. eapply IHs. intro. destruct H0. simpl; eauto. 
  intros.
  specialize (set_mem_complete2 string_dec _ _ H1). intro.
  induction s1. simpl. 
  rewrite H2; eauto. simpl. 
  destruct (string_dec x a). simpl.
  rewrite e in H2. erewrite H2; eauto.
  simpl. destruct (in_dec string_dec a s2).
  erewrite (set_mem_correct2 string_dec _ _ i).
  f_equal. eauto.
  erewrite (set_mem_complete2 string_dec _ _ n0).
  eauto.
Qed.


Lemma intersection_doesnt_contain_cons :
  forall (s: set ident)
    (a: ident)
    (s2: set ident),
    set_inter string_dec (a :: s) s2 = nil ->
    ~ In a s2.
Proof.
  induction s; intros.
  - simpl in H. destruct (set_mem string_dec a s2) eqn:M.
    invs H.
    eapply set_mem_complete1 in M. assumption.
  - simpl in H. destruct (set_mem string_dec a0 s2) eqn:M0.
    invs H.
    destruct (set_mem string_dec a s2) eqn:M.
    invs H.
    eapply IHs. simpl. rewrite M0. eassumption.
Qed.

Lemma intersection_doesnt_contain :
  forall (s: set ident)
    (x: ident)
    (s2: set ident),
  set_inter string_dec (set_add string_dec x s)
            s2 = nil ->
  ~ In x s2.
Proof.
  induction s; intros.
  - simpl in H. destruct (set_mem string_dec x s2) eqn:M; try congruence.
    eapply set_mem_complete1 in M. eassumption.
  - simpl in H. destruct (string_dec x a).
    + subst. eapply intersection_doesnt_contain_cons in H. eassumption.
    + simpl in H. destruct (set_mem string_dec a s2) eqn:M.
      invs H.
      eapply IHs. eassumption.
Qed.

Local Open Scope bool_scope.

Ltac destruct_not_or :=
  repeat match goal with
         | [ H: _ || _ = false |- _ ] =>
             eapply orb_false_elim in H; destruct H
         | [ H: ~ In _ (set_union _ _ _) |- _ ] =>
             eapply not_in_set_union in H; destruct H
         | [ H: ~ In _ (set_add _ _ _) |- _ ] =>
             eapply not_in_set_add in H; destruct H
         end.


Lemma not_in_fold_left_union_not_in_fold :
  forall (T: Type)
    (f: T -> set ident)
    (a_list: list T)
    (s: set ident)
    (x: ident),
    ~ In x (fold_left (fun (acc : set ident) (v : T) =>
                         set_union string_dec acc (f v))
                      a_list s) <->
    ~ In x (set_union string_dec (fold_left (fun (acc: set ident) (v: T) =>
                                               set_union string_dec acc (f v))
                                            a_list nil)
                      s).
Proof.
  induction a_list; intros; split; intros.
  - simpl. simpl in H. eapply not_in_sets_not_in_set_union; eauto.
  - simpl. simpl in H. eapply not_in_set_union in H. destruct H. assumption.
  - simpl in H. eapply IHa_list in H. simpl. eapply not_in_set_union in H.
    destruct H. eapply not_in_set_union in H0. destruct H0.
    eapply not_in_sets_not_in_set_union.
    + eapply IHa_list. eapply not_in_sets_not_in_set_union.
      * eassumption.
      * eapply not_in_sets_not_in_set_union; eauto.
    + eassumption.
  - simpl in H. simpl. eapply IHa_list. eapply not_in_set_union in H.
    destruct H. eapply IHa_list in H. eapply not_in_set_union in H.
    destruct H. eapply not_in_sets_not_in_set_union.
    + eassumption.
    + eapply not_in_sets_not_in_set_union.
      eauto.
      eapply not_in_set_union in H1. destruct H1. eauto.
Qed.

Lemma not_in_fold_left_not_in_fold :
  forall (T: Type) (x: ident) a_list,
    forall (f: T -> set ident),
    (forall (s: set ident),
    ~
      In x
        (fold_left
           (fun (acc : set ident) (v : T) =>
            set_union string_dec acc (f v)) a_list
           s) ->
    ~ In x (fold_left (fun (acc : set ident) (v : T) =>
                         set_union string_dec acc (f v)) a_list nil))
    /\
      (forall (s: set ident),
           ~ In x
        (fold_left
           (fun (acc : set ident) (v : T) =>
            set_union string_dec acc (f v)) a_list
           s) ->
           ~ In x s).
Proof.
  induction a_list; split; intros.
  - eauto.
  - simpl in H. eauto.
  - specialize (IHa_list f). destruct IHa_list as (IH1 & IH2).
    simpl in H.
    simpl. simpl in H. pose proof (H' := H). eapply IH1 in H.
    eapply IH2 in H'.
    eapply not_in_fold_left_union_not_in_fold.
    eapply not_in_sets_not_in_set_union.
    + eassumption.
    + eapply not_in_set_union in H'. eapply not_in_sets_not_in_set_union; eauto.
      eapply H'.
  - simpl in H. eapply not_in_fold_left_union_not_in_fold in H.
    destruct_not_or. assumption.
Qed.

Lemma not_in_fold_left_not_in_fold1 :
  forall (T: Type) (x: ident) a_list,
    forall (f: T -> set ident),
    (forall (s: set ident),
    ~
      In x
        (fold_left
           (fun (acc : set ident) (v : T) =>
            set_union string_dec acc (f v)) a_list
           s) ->
    ~ In x (fold_left (fun (acc : set ident) (v : T) =>
                         set_union string_dec acc (f v)) a_list nil)).
Proof.
  eapply not_in_fold_left_not_in_fold.
Qed.

Lemma not_in_fold_left_not_in_fold2 :
  forall (T U: Type) (Ueq_dec: forall (u1 u2: U), {u1 = u2} + {u1 <> u2}) (x: U)
    (a_list: list T),
  forall (f: T -> set U),
    (forall (s: set U),
        ~ In x
          (fold_left
             (fun (acc : set U) (v : T) =>
                set_union Ueq_dec acc (f v)) a_list
             s) ->
           ~ In x s).
Proof.
  eapply not_in_fold_left_not_in_fold.
Qed.*)

Lemma in_set_union_gen :
  forall (T: Type) (Teq_dec: forall (t1 t2: T), {t1 = t2} + {t1 <> t2})
    (P: T -> Prop) (s1 s2: ListSet.set T),
    (forall z : T,
        In z
           (ListSet.set_union Teq_dec s1 s2) -> P z) ->
    (forall z: T,
        In z s1 -> P z) /\ (forall z : T,
                             In z s2 -> P z).
Proof.
  intros.
  split; intros.
  + eapply ListSet.set_union_intro1 in H0. eapply H; eauto.
  + eapply ListSet.set_union_intro2 in H0; eapply H; eauto.
Qed.

Lemma in_init_in_fold_left_union :
  forall (T T': Type) (l: list T) (f: T -> ListSet.set T') (T'eq_dec : forall (t1 t2: T'), { t1 = t2} + { t1 <> t2 }) (init: ListSet.set T') (t': T'),
    In t' init ->
    In t' (fold_left (fun acc t =>
                        ListSet.set_union T'eq_dec acc (f t))
                     l
                     init).
Proof.
  induction l; intros.
  - simpl. eauto.
  - simpl. eapply IHl; eauto.
    eapply ListSet.set_union_iff. eauto.
Qed.

Lemma in_fold_left_iff :
  forall (T T': Type) (l: list T) (f: T -> ListSet.set T') (T'eq_dec : forall (t1 t2: T'), { t1 = t2 } + { t1 <> t2 }) (init: ListSet.set T') (t': T'),
    In t' (fold_left (fun acc t =>
                        ListSet.set_union T'eq_dec acc (f t))
                     l init) <->
      In t' (fold_left (fun acc t =>
                          ListSet.set_union T'eq_dec acc (f t))
                       l nil) \/
        In t' init.
Proof.
  induction l; split; intros.
  - simpl in H. eauto.
  - simpl. destruct H; eauto; invs H.
  - simpl in H. eapply IHl in H. destruct H.
    + left. simpl. eapply IHl. eauto.
    + eapply ListSet.set_union_iff in H. destruct H.
      * simpl. eauto.
      * simpl. left. eapply IHl. right. eapply ListSet.set_union_iff. eauto.
  - simpl in H. destruct H.
    + simpl. eapply IHl in H. destruct H.
      * eapply IHl. left. eauto.
      * eapply ListSet.set_union_iff in H. destruct H; try invs H.
        eapply IHl. right. eapply ListSet.set_union_iff; eauto.
    + simpl. eapply IHl. right. eapply ListSet.set_union_iff. eauto.
Qed.

Lemma in_fold_left_in_fold :
  forall (T T': Type) (l: list T) (f: T -> ListSet.set T') (T'eq_dec : forall (t1 t2: T'), { t1 = t2 } + {t1 <> t2}) (init: ListSet.set T') (t' : T'),
    In t' (fold_left (fun acc t =>
                        ListSet.set_union T'eq_dec acc (f t))
                     l
                     nil) ->
    In t' (fold_left (fun acc t =>
                        ListSet.set_union T'eq_dec acc (f t))
                     l
                     init).
Proof.
  intros. eapply in_fold_left_iff. left. eauto.
Qed.

Lemma in_fold_left_elim :
  forall (T T': Type) (l: list T) (f: T -> ListSet.set T') (T'eq_dec : forall (t1 t2: T'), { t1 = t2 } + { t1 <> t2 }) (init: ListSet.set T') (t': T'),
    In t' (fold_left (fun acc t =>
                        ListSet.set_union T'eq_dec acc (f t))
                     l init) ->
    In t' (fold_left (fun acc t =>
                        ListSet.set_union T'eq_dec acc (f t))
                     l nil) \/
      In t' init.
Proof.
  intros. eapply in_fold_left_iff in H. eauto.
Qed.

Lemma in_fold_left_intro :
  forall (T T': Type) (l: list T) (f: T -> ListSet.set T') (T'eq_dec : forall (t1 t2: T'), { t1 = t2 } + { t1 <> t2 }) (init: ListSet.set T') (t': T'),
    In t' (fold_left (fun acc t =>
                        ListSet.set_union T'eq_dec acc (f t))
                     l nil) \/
      In t' init ->
    In t' (fold_left (fun acc t =>
                        ListSet.set_union T'eq_dec acc (f t))
                     l init).
Proof.
  intros. eapply in_fold_left_iff in H. eauto.
Qed.

