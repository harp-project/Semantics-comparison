From CE Require Export FBOS NOS PBOS.

Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.

(* Section indhyp.

Axiom Expression_ind_2 :
forall P : Expression -> Prop,
       (forall l : Literal, P (ELit l)) ->
       (forall v : Var, P (EVar v)) ->
       (forall f2 : FunctionIdentifier, P (EFunId f2)) ->
       (forall (vl : list Var) (e : Expression), P e -> P (EFun vl e)) ->
       (forall (f6 : string) (l : list Expression), 
         (forall i : nat, i < length l -> P (nth i l ErrorExp)) ->
       P (ECall f6 l)) ->
       (forall exp : Expression, P exp ->
        forall l : list Expression,
         (forall i : nat, i < length l -> P (nth i l ErrorExp)) ->
        P (EApp exp l)) ->
       (forall (v : Var) (e1 : Expression),
        P e1 -> forall e2 : Expression, P e2 -> P (ELet v e1 e2)) ->
       (forall (f10 : FunctionIdentifier) (l : list Var) (b : Expression),
        P b -> forall e : Expression, P e -> P (ELetRec f10 l b e)) ->
       (forall e1 : Expression,
        P e1 ->
        forall (v1 : Var) (e2 : Expression),
        P e2 -> forall (vl2 : list Var) (e3 : Expression), P e3 -> P (ETry e1 v1 e2 vl2 e3)) ->
       forall e : Expression, P e.

End indhyp. *)

Theorem clock_list_increase :
forall l env id eff id' res eff' clock,
(forall (env : Environment) (id : nat) (exp : Expression) 
            (eff : SideEffectList) (id' : nat) (res : Value + Exception)
            (eff' : SideEffectList),
          eval_fbos_expr clock env id exp eff = Result id' res eff' ->
          eval_fbos_expr (S clock) env id exp eff = Result id' res eff') ->
  eval_elems (eval_fbos_expr clock) env id l eff = LResult id' res eff'
->
  eval_elems (eval_fbos_expr (S clock)) env id l eff = LResult id' res eff'.
Proof.
  induction l; intros.
  * simpl. inversion H0. subst. auto.
  * simpl in H0. case_eq (eval_fbos_expr clock env id a eff); intros. destruct res0.
    - rewrite H1 in H0. apply H in H1.
      remember (S clock) as cl. simpl. rewrite H1.
      rewrite Heqcl in *.
      case_eq (eval_elems (eval_fbos_expr clock) env id0 l eff0); intros.
      + pose (IHl _ _ _ _ _ _ _ H H2). rewrite e. rewrite H2 in H0. inversion H0. reflexivity.
      + rewrite H2 in H0. congruence.
      + rewrite H2 in H0. congruence.
    - rewrite H1 in H0. apply H in H1. inversion H0. subst.
      remember (S clock) as cl. simpl. rewrite H1. auto.
    - rewrite H1 in H0. congruence.
    - rewrite H1 in H0. congruence.
Qed.

Theorem clock_increase :
  forall clock env id exp eff id' res eff',
  eval_fbos_expr clock env id exp eff = Result id' res eff'
->
  eval_fbos_expr (S clock) env id exp eff = Result id' res eff'.
Proof.
  induction clock; intros; subst.
  * simpl in H. inversion H.
  * destruct exp.
    - simpl in *. inversion H. auto.
    - simpl in *. inversion H. auto.
    - simpl in *. inversion H. auto.
    - simpl in *. inversion H. auto.
    - simpl in H. case_eq (eval_elems (eval_fbos_expr clock) env id l eff); intros.
      destruct res0.
      + rewrite H0 in H. case_eq (eval f l0 eff0); intros. inversion H. subst.
        apply clock_list_increase in H0. remember (S clock) as cl. simpl.
        rewrite H0. reflexivity. auto.
      + rewrite H0 in H. inversion H. subst.
        apply clock_list_increase in H0.
        remember (S clock) as cl. simpl.
        rewrite H0. reflexivity. auto.
      + rewrite H0 in H. congruence.
      + rewrite H0 in H. congruence.
  - simpl in H. case_eq (eval_fbos_expr clock env id exp eff); intros. destruct res0.
    + rewrite H0 in H. case_eq (eval_elems (eval_fbos_expr clock) env id0 l eff0); intros.
      destruct res0.
      ** rewrite H1 in H. apply clock_list_increase in H1. 2: auto. apply IHclock in H0.
         remember (S clock) as cl. simpl. rewrite H0. rewrite H1.
         destruct v; inversion H; subst; auto.
         destruct ((Datatypes.length vl =? Datatypes.length l0)%nat); auto.
         apply IHclock in H3. rewrite H3. rewrite H. auto.
      ** rewrite H1 in H. inversion H.
         apply IHclock in H0.
         apply clock_list_increase in H1. 2: auto.
         remember (S clock) as cl. simpl. rewrite H0. rewrite H1. subst. auto.
      ** rewrite H1 in H. congruence.
      ** rewrite H1 in H. congruence.
    + rewrite H0 in H. inversion H. subst. remember (S clock) as cl. simpl.
      apply IHclock in H0.
      rewrite H0. reflexivity.
    + rewrite H0 in H. discriminate.
    + rewrite H0 in H. discriminate.
  - simpl in H. case_eq (eval_fbos_expr clock env id exp1 eff); intros. destruct res0.
    + rewrite H0 in H. remember (S clock) as cl. simpl.
      case_eq (eval_fbos_expr cl env id exp1 eff); intros. destruct res0.
      ** apply IHclock in H0. rewrite H0 in H1. inversion H1. subst. apply IHclock in H. assumption.
      ** apply IHclock in H0. rewrite H0 in H1. inversion H1.
      ** apply IHclock in H0. congruence.
      ** apply IHclock in H0. congruence.
    + rewrite H0 in H. inversion H. subst. remember (S clock) as cl.
      apply IHclock in H0. simpl. rewrite H0. auto.
    + rewrite H0 in H. congruence.
    + rewrite H0 in H. congruence.
  - simpl in H. remember (S clock) as cl. simpl. apply IHclock in H. assumption.
  - simpl in H. case_eq (eval_fbos_expr clock env id exp1 eff); intros. destruct res0.
    + rewrite H0 in H. remember (S clock) as cl. simpl.
      case_eq (eval_fbos_expr cl env id exp1 eff); intros. destruct res0.
      ** apply IHclock in H0. rewrite H0 in H1. inversion H1. subst. apply IHclock in H. assumption.
      ** apply IHclock in H0. rewrite H0 in H1. inversion H1.
      ** apply IHclock in H0. congruence.
      ** apply IHclock in H0. congruence.
    + rewrite H0 in H. inversion H. subst. remember (S clock) as cl.
      apply IHclock in H0. simpl. rewrite H0.
      destruct (Datatypes.length vl2 =? 2)%nat;
      rewrite H; apply IHclock in H2; rewrite H2; auto.
    + rewrite H0 in H. congruence.
    + rewrite H0 in H. congruence.
Qed.

Theorem bigger_clock :
  forall clock clock' env id exp eff id' res eff',
  clock <= clock' ->
  eval_fbos_expr clock env id exp eff = Result id' res eff'
->
  eval_fbos_expr clock' env id exp eff = Result id' res eff'.
Proof.
  intros. induction H.
  * assumption. 
  * apply clock_increase. auto.
Qed.

Theorem bigger_list_clock :
  forall clock clock' env id exps eff id' res eff',
  clock <= clock' ->
  eval_elems (eval_fbos_expr clock) env id exps eff = LResult id' res eff'
->
  eval_elems (eval_fbos_expr clock') env id exps eff = LResult id' res eff'.
Proof.
  intros. induction H.
  * assumption.
  * apply clock_list_increase. 2: auto. intros. auto.
    apply clock_increase in H1. assumption.
Qed.

Lemma restrict env a id' v' eff' (params : list Expression) (x0: list nat) x x1 id eff1:
(forall i : nat,
    i < Datatypes.length (a :: params) ->
    exists clock : nat,
      eval_fbos_expr clock env (nth_def (id' :: x0) id 0 i) (nth i (a :: params) ErrorExp)
        (nth_def (eff' :: x1) eff1 [] i) =
      Result (nth_def (id' :: x0) id 0 (S i)) (inl (nth i (v' :: x) ErrorValue))
        (nth_def (eff' :: x1) eff1 [] (S i)))
->
  (forall i : nat,
    i < Datatypes.length params ->
    exists clock : nat,
      eval_fbos_expr clock env (nth_def x0 id' 0 i) (nth i params ErrorExp)
        (nth_def x1 eff' [] i) =
      Result (nth_def x0 id' 0 (S i)) (inl (nth i x ErrorValue))
        (nth_def x1 eff' [] (S i))).
Proof.
  intros.
  assert (S i < Datatypes.length (a :: params)) as A1.
  { simpl. lia. } pose (E := H (S i) A1). 
  destruct E. simpl nth_def in H1. simpl nth in H. exists x2. simpl. exact H1.
Qed.

Theorem list_sound :
forall params env ids id eff vals eff1,
(forall i : nat,
     i < Datatypes.length params ->
     exists clock : nat,
       eval_fbos_expr clock env (nth_def ids id 0 i) (nth i params ErrorExp)
         (nth_def eff eff1 [] i) =
       Result (nth_def ids id 0 (S i)) (inl (nth i vals ErrorValue))
         (nth_def eff eff1 [] (S i)))
-> Datatypes.length params = Datatypes.length vals
-> Datatypes.length params = Datatypes.length ids
-> Datatypes.length params = Datatypes.length eff
->
  exists clock', eval_elems (eval_fbos_expr clock') env id params eff1 = LResult (last ids id) (inl vals) (last eff eff1).
Proof.
  induction params.
  * intros. exists 1. simpl. apply eq_sym, length_zero_iff_nil in H0.
    apply eq_sym, length_zero_iff_nil in H1. apply eq_sym, length_zero_iff_nil in H2.
    subst. auto.
  * intros.
    pose (EE1 := element_exist _ _ H0).
    pose (EE2 := element_exist _ _ H1).
    pose (EE3 := element_exist _ _ H2).
    inversion EE1 as [v']. inversion EE2 as [id']. inversion EE3 as [eff'].
    destruct H3. destruct H4. destruct H5.
    clear EE1. clear EE2. clear EE3. subst.
    simpl length in *. apply eq_add_S in H0. apply eq_add_S in H1. apply eq_add_S in H2.
    pose (IHparams _ _ _ _ _ _ (restrict _ _ _ _ _ _ _ _ _ _ _ H) H0 H1 H2). destruct e.
    pose (H 0 (Nat.lt_0_succ _)). destruct e.
    exists (x2 + x3).
    simpl in H4. (* rewrite Heqcl in *. *)
    apply bigger_clock with (clock' := x2 + x3) in H4. 2: lia.
    apply bigger_list_clock with (clock' := x2 + x3) in H3. 2: lia.
    simpl eval_elems. rewrite H4, H3.
    rewrite last_element_equal with (def2 := id).
    rewrite last_element_equal with (def2 := eff1). auto.
Qed.

Lemma restrict2 env i id'' x1 id a params eff' x0 eff1 v' x:
(forall j : nat,
    j < S i ->
    exists clock : nat,
      eval_fbos_expr clock env (nth_def (id'' :: x1) id 0 j) (nth j (a :: params) ErrorExp)
        (nth_def (eff' :: x0) eff1 [] j) =
      Result (nth_def (id'' :: x1) id 0 (S j)) (inl (nth j (v' :: x) ErrorValue))
        (nth_def (eff' :: x0) eff1 [] (S j)))
->
(forall j : nat,
    j < i ->
    exists clock : nat,
      eval_fbos_expr clock env (nth_def (x1) id'' 0 j) (nth j (params) ErrorExp)
        (nth_def (x0) eff' [] j) =
      Result (nth_def (x1) id 0 (S j)) (inl (nth j (x) ErrorValue))
        (nth_def (x0) eff' [] (S j))).
Proof.
  intros.
  assert (S j < S i) as A1.
  { simpl. lia. } pose (E := H (S j) A1). 
  destruct E. simpl nth_def in H1. simpl nth in H. exists x2. simpl. exact H1.
Qed.

Theorem list_exception_sound :
forall params env ids id eff vals eff1 eff2 id' ex i,
(forall j : nat,
     j < i ->
     exists clock : nat,
       eval_fbos_expr clock env (nth_def ids id 0 j) (nth j params ErrorExp)
         (nth_def eff eff1 [] j) =
       Result (nth_def ids id 0 (S j)) (inl (nth j vals ErrorValue))
         (nth_def eff eff1 [] (S j)))
->
i < Datatypes.length params ->
Datatypes.length vals = i ->
Datatypes.length eff = i ->
Datatypes.length ids = i ->
| env, last ids id, nth i params ErrorExp, last eff eff1 | -e> | id', inr ex, eff2 | ->
(exists clock : nat,
                eval_fbos_expr clock env (last ids id) (nth i params ErrorExp) (last eff eff1) =
                Result id' (inr ex) eff2)
->
(exists clock', eval_elems (eval_fbos_expr clock') env id params eff1 = LResult id' (inr ex) eff2).
Proof.
  induction params; intros.
  * inversion H0.
  * destruct i.
    - simpl in H4, H5. destruct H5. exists x. simpl.
      apply length_zero_iff_nil in H1.
      apply length_zero_iff_nil in H2.
      apply length_zero_iff_nil in H3. subst.
      simpl in H5. rewrite H5. auto.
    - pose (element_exist _ _ (eq_sym H1)).
      pose (element_exist _ _ (eq_sym H2)).
      pose (element_exist _ _ (eq_sym H3)).
      destruct e as [v']. destruct e0 as [eff']. destruct e1 as [id''].
      destruct H6. destruct H7. destruct H8.
      subst. destruct H5.
      pose (H 0 (Nat.lt_0_succ _)). destruct e. simpl in H6.
      simpl in H0. apply Lt.lt_S_n in H0.
      apply eq_add_S in H1. apply eq_add_S in H2. apply eq_add_S in H3.
      rewrite <- last_element_equal, <- last_element_equal in H4, H5.
      assert (exists x2, eval_fbos_expr x2 env (last x1 id'') (nth (S i) (a :: params) ErrorExp) (last x0 eff') =
     Result id' (inr ex) eff2). { eexists. exact H5. }
      pose (IHparams _ _ _ _ _ _ _ _ _ _ (restrict2 _ _ _ _ _ _ _ _ _ _ _ _ H) H0 H1 H2 H3 H4 H7). destruct e.
      exists (x3 + x4). simpl.
      apply bigger_clock with (clock' := x3 + x4) in H6.
      apply bigger_list_clock with (clock' := x3 + x4) in H8.
      2-3: lia.
      rewrite H6, H8. auto.
Qed.

Theorem fbos_sound :
  forall env id exp eff id' res eff',
  | env, id, exp, eff | -e> |id', res, eff'|
->
  (exists clock, eval_fbos_expr clock env id exp eff = Result id' res eff').
Proof.
  intro. intro. intros. induction H.
  1-4: exists 2; simpl; auto; rewrite H; auto.
  * apply list_sound in H3; auto. destruct H3. exists (S x).
    simpl. rewrite H3. subst.
    rewrite H4 at 2. rewrite H4 at 1. simpl. auto.
  * destruct IHeval_expr1.
    apply list_sound in H5; auto.
    destruct H5. destruct IHeval_expr2.
    exists (S (x + x0 + x1)).
    simpl.
    apply bigger_clock with (clock' := x + x0 + x1) in H7.
    apply bigger_clock with (clock' := x + x0 + x1) in H8.
    apply bigger_list_clock with (clock' := x + x0 + x1) in H5.
    rewrite H7, H5.
    apply Nat.eqb_eq in H1. rewrite H1.
    rewrite H8 at 1. reflexivity.
    1-3: lia.
  * destruct IHeval_expr1, IHeval_expr2.
    exists (S (x + x0)).
    apply bigger_clock with (clock' := x + x0) in H1.
    apply bigger_clock with (clock' := x + x0) in H2.
    2-3: lia.
    simpl. rewrite H1. auto.
  * destruct IHeval_expr.
    exists (S x). simpl. auto.
  * destruct IHeval_expr1, IHeval_expr2.
    exists (S (x + x0)).
    apply bigger_clock with (clock' := x + x0) in H1.
    apply bigger_clock with (clock' := x + x0) in H2.
    2-3: lia.
    simpl. rewrite H1. auto.
  * destruct IHeval_expr1, IHeval_expr2.
    exists (S (x + x0)).
    apply bigger_clock with (clock' := x + x0) in H1.
    apply bigger_clock with (clock' := x + x0) in H2.
    2-3: lia.
    simpl. rewrite H1. auto.
  * eapply list_exception_sound in H4; auto.
    - destruct H4. exists (S x). simpl. rewrite H4. reflexivity.
    - exact H5.
    - exact IHeval_expr.
  * destruct IHeval_expr.
    exists (S x). simpl. rewrite H0. auto.
  * destruct IHeval_expr1.
    eapply list_exception_sound in H5; auto.
    - destruct H5. exists (S (x + x0)).
      simpl.
      apply bigger_clock with (clock' := x + x0) in H7. rewrite H7.
      apply bigger_list_clock with (clock' := x + x0) in H5. rewrite H5.
      reflexivity. 
      1-2: lia.
    - auto.
    - auto.
  * destruct IHeval_expr.
    apply list_sound in H4; auto.
    destruct H4.
    exists (S (x + x0)).
    simpl.
    apply bigger_clock with (clock' := x + x0) in H8; try lia.
    apply bigger_list_clock with (clock' := x + x0) in H4; try lia.
    rewrite H8, H4.
    destruct v.
    - subst. auto.
    - congruence.
  * destruct IHeval_expr.
    apply list_sound in H4; auto.
    destruct H4.
    exists (S (x + x0)).
    simpl.
    apply bigger_clock with (clock' := x + x0) in H8; try lia.
    apply bigger_list_clock with (clock' := x + x0) in H4; try lia.
    rewrite H8, H4.
    apply Nat.eqb_neq in H5. rewrite H5.
    subst. auto.
  * destruct IHeval_expr. exists (S x).
    simpl. rewrite H0. auto.
Qed.

Lemma list_correct :
forall {l env id eff id' vl eff' clock},
eval_elems (eval_fbos_expr clock) env id l eff = LResult id' (inl vl) eff'
->
(
exists idl effl, 
  length l = length vl /\
  length l = length idl /\
  length l = length effl /\
  eff' = last effl eff /\
  id' = last idl id /\
  (forall i, i < length l ->
    eval_fbos_expr clock env (nth_def idl id 0 i) (nth i l ErrorExp) (nth_def effl eff [] i) =
      Result (nth_def idl id 0 (S i)) (inl (nth i vl ErrorValue)) (nth_def effl eff [] (S i))
  )
)
.
Proof.
  induction l; intros.
  * inversion H. subst. exists []. exists [].
    repeat (split; auto).
    intros. inversion H0.
  * simpl in H.
    case_eq (eval_fbos_expr clock env id a eff); intros. destruct res.
    - rewrite H0 in H. case_eq (eval_elems (eval_fbos_expr clock) env id0 l eff0); intros. destruct res.
         + rewrite H1 in H. inversion H. subst.
           pose (IHl _ _ _ _ _ _ _ H1). inversion e. inversion H2.
           destruct H3, H4, H5, H6, H7.
           exists (id0 :: x). exists (eff0 :: x0).
           split. 2: split. 3: split. 4: split. 5: split.
           1-3 : simpl; lia.
           ** rewrite last_element_equal with (def2 := eff) in H6. auto.
           ** rewrite last_element_equal with (def2 := id) in H7. auto.
           ** intros. destruct i.
             -- simpl. assumption.
             -- simpl in H9. 
                (* setoid failure for simple rewrite *)
                assert (i < length l). { lia. }
                apply H8. assumption.
         + rewrite H1 in H. discriminate.
         + rewrite H1 in H. discriminate.
         + rewrite H1 in H. discriminate.
    - rewrite H0 in H. discriminate.
    - rewrite H0 in H. discriminate.
    - rewrite H0 in H. discriminate.
Qed.

Lemma list_exception_correct :
forall {l env id eff id' ex eff' clock},
eval_elems (eval_fbos_expr clock) env id l eff = LResult id' (inr ex) eff'
->
(
exists vals idl effl, 
  length vals < length l /\
  length vals = length idl /\
  length vals = length effl /\
  (forall i, i < length vals ->
    eval_fbos_expr clock env (nth_def idl id 0 i) (nth i l ErrorExp) (nth_def effl eff [] i) =
      Result (nth_def idl id 0 (S i)) (inl (nth i vals ErrorValue)) (nth_def effl eff [] (S i))
  ) /\
  eval_fbos_expr clock env (last idl id) (nth (length vals) l ErrorExp) (last effl eff) = Result id' (inr ex) eff'
)
.
Proof.
  induction l; intros.
  * inversion H.
  * simpl in H.
    case_eq (eval_fbos_expr clock env id a eff); intros. destruct res.
    - rewrite H0 in H.
      case_eq (eval_elems (eval_fbos_expr clock) env id0 l eff0); intros. destruct res.
         + rewrite H1 in H. inversion H.
         + rewrite H1 in H. inversion H. subst.
           pose (IHl env id0 eff0 id' ex eff' clock H1).
           destruct e. destruct H2, H2.
           destruct H2, H3, H4, H5.
           exists (v::x). exists (id0::x0). exists (eff0::x1).
           split. 2: split. 3: split. 4: split.
           all: try (simpl; lia).
           ** intros. destruct i.
             -- simpl. assumption.
             -- apply H5. simpl in H7. lia.
           ** rewrite last_element_equal with (def2 := id) in H6.
              rewrite last_element_equal with (def2 := eff) in H6.
              assumption.
         + rewrite H1 in H. congruence.
         + rewrite H1 in H. congruence.
    - rewrite H0 in H. inversion H. subst.
      exists []. exists []. exists [].
      split. 2: split. 3: split. 4: split.
      all: auto.
      + simpl. lia.
      + intros. inversion H1. 
    - rewrite H0 in H. discriminate.
    - rewrite H0 in H. discriminate.
Qed.

Theorem fbos_correct :
  forall clock exp env id eff id' res eff',
  (eval_fbos_expr clock env id exp eff = Result id' res eff')
->
  | env, id, exp, eff | -e> |id', res, eff'|.
Proof.
  induction clock; intros.
  * inversion H.
  * destruct exp.
    - inversion H. apply eval_lit.
    - inversion H. apply eval_var. auto.
    - inversion H. apply eval_funid. auto.
    - inversion H. apply eval_fun.
    - simpl in H. case_eq (eval_elems (eval_fbos_expr clock) env id l eff); intros; rewrite H0 in H.
      + destruct res0.
        ** apply list_correct in H0. destruct H0, H0, H0, H1, H2, H3, H4.
           eapply eval_call. exact H0. exact H2. exact H1.
           intros. pose (H5 i H6). apply IHclock in e. auto.
           inversion H. rewrite <- surjective_pairing. rewrite H3. auto.
           inversion H. subst. auto.
        ** apply list_exception_correct in H0. inversion H. subst.
           destruct H0, H0, H0, H0, H1, H2, H3.
           eapply eval_call_ex with (vals := x) (ids := x0) (eff := x1).
           exact H0. auto. auto. auto. intros. pose (H3 j H5). apply IHclock in e0. auto.
           apply IHclock in H4. auto.
      + congruence.
      + congruence.
    - simpl in H. case_eq (eval_fbos_expr clock env id exp eff); intros; rewrite H0 in H.
      + destruct res0.
        ** case_eq (eval_elems (eval_fbos_expr clock) env id0 l eff0); intros; rewrite H1 in H.
           destruct res0.
           -- apply IHclock in H0. apply list_correct in H1.
              destruct H1, H1, H1, H2, H3, H4, H5.
              destruct v.
              ++ inversion H. subst.
                 eapply eval_app_badfun_ex with (vals := l0) (ids := x) (eff := x0); auto.
                 exact H0. congruence.
              ++ case_eq ((Datatypes.length vl =? Datatypes.length l0)%nat); intros; rewrite H7 in *.
                 *** apply IHclock in H. eapply eval_app with (vals := l0) (ids := x) (eff := x0); auto.
                     exact H0.
                     apply Nat.eqb_eq in H7. auto.
                     rewrite <- H4, <- H5. exact H.
                 *** inversion H. subst. apply Nat.eqb_neq in H7.
                     eapply eval_app_badarity_ex with (vals := l0) (ids := x) (eff := x0); auto.
                     exact H0.
           -- inversion H. subst.
              apply list_exception_correct in H1. destruct H1, H1, H1, H1, H2, H3, H4.
              eapply eval_app_param_ex with (vals := x) (ids := x0) (eff := x1); auto.
              auto.
              apply IHclock in H0. exact H0.
           -- congruence.
           -- congruence.
        ** inversion H. subst. apply eval_app_closure_ex. apply IHclock in H0. auto.
      + congruence.
      + congruence.
    - simpl in H. case_eq (eval_fbos_expr clock env id exp1 eff); intros; rewrite H0 in H.
      destruct res0.
      + apply IHclock in H0. apply IHclock in H.
        eapply eval_let. exact H0. exact H.
      + apply IHclock in H0. inversion H. subst. eapply eval_let_ex. auto.
      + congruence.
      + congruence.
    - apply IHclock in H. eapply eval_letrec. exact H.
    - simpl in H. case_eq (eval_fbos_expr clock env id exp1 eff); intros; rewrite H0 in H.
      destruct res0.
      + apply IHclock in H0. apply IHclock in H.
        eapply eval_try. exact H0. auto.
      + apply IHclock in H. apply IHclock in H0. eapply eval_catch.
        exact H0. exact H.
      + congruence.
      + congruence.
Qed.

(** determinism is trivial *)
Theorem fbos_deterministic :
  forall env id exp eff clock r r',
  eval_fbos_expr clock env id exp eff = r ->
  eval_fbos_expr clock env id exp eff = r' ->
  r = r'.
Proof.
  intros. rewrite H in H0. auto.
Qed.


Example eq1 env id e eff clock x :
  eval_fbos_expr clock env (S id) e eff = eval_fbos_expr (S (S clock)) env id (ELet x (EFun [] e) (EApp (EVar x) [])) eff.
Proof.
  destruct clock.
  * simpl. reflexivity.
  * simpl eval_fbos_expr at 2. rewrite get_value_here. rewrite nil_length. repeat (fold eval_fbos_expr). reflexivity.
Qed.

Import List.

Arguments eval : simpl never.

Example eq2 env id eff clock A B e1 e2 v1 v2 eff1 eff2 id1 id2 t:
  eval_fbos_expr clock env id e1 eff = Result (id + id1) (inl v1) (eff ++ eff1) ->
  eval_fbos_expr clock env id e2 eff = Result (id + id2) (inl v2) (eff ++ eff2) ->
  eval_fbos_expr clock (insert_value env (inl B) v2) (id + id2) e1 (eff ++ eff2) = Result (id + id2 + id1) (inl v1) (eff ++ eff2 ++ eff1) ->
  eval_fbos_expr clock (insert_value env (inl A) v1) (id + id1) e2 (eff ++ eff1) = Result (id + id1 + id2) (inl v2) (eff ++ eff1 ++ eff2) ->
  A <> B ->
  eval_fbos_expr (S (S clock)) env id 
      (ELet B e2 (ELet A e1
        (ECall "+"%string [EVar A ; EVar B])))
      eff = Result (id + id2 + id1) (inl t) (eff ++ eff2 ++ eff1)
<->
  eval_fbos_expr (S (S clock)) env id 
      (ELet A e1 (ELet B e2
        (ECall "+"%string [EVar A ; EVar B])))
      eff = Result (id + id1 + id2) (inl t) (eff ++ eff1 ++ eff2).
Proof.
  intros. remember (S clock) as cl.
  simpl.
  pose (C1 := clock_increase _ _ _ _ _ _ _ _ H). rewrite <- Heqcl in C1.
  rewrite C1.
  pose (C2 := clock_increase _ _ _ _ _ _ _ _ H0). rewrite <- Heqcl in C2.
  rewrite C2.
  rewrite Heqcl in *. simpl.
  rewrite H1, H2.
  destruct clock.
  * simpl. split; discriminate.
  * simpl. destruct clock.
    - simpl. split; discriminate.
    - simpl. rewrite get_value_here, get_value_there, get_value_here.
      rewrite get_value_here, get_value_there, get_value_here.
      2-3: congruence.
      destruct v1, v2.
      all: try (split; intros; discriminate).
      all: try (destruct l).
      all: try (split; intros; discriminate).
      all: try (destruct l0).
      all: try (split; intros; discriminate).
      split; intros; inversion H4; subst; reflexivity.
Qed.

Example eq1_pbs env id e eff id' res eff' x:
 |env, (S id), e, eff | -p> | id', res, eff' |
<->
 |env, id, ELet x (EFun [] e) (EApp (EVar x) []), eff| -p> |id', res, eff'|.
Proof.
  split; intros.
  * eapply peval_let.
    - apply peval_fun.
    - apply peval_let_fin. simpl. eapply peval_app.
      + eapply peval_var. rewrite get_value_here. reflexivity.
      + eapply peval_app1_fin.
        ** eapply peval_empty.
        ** eapply peval_app2_fin; auto.
  * inversion H; subst. inversion H9. inversion H10; subst.
    - inversion H14.
    - inversion H14. subst. inversion H19. subst.
      inversion H4. simpl in H3. rewrite get_value_here in H3. subst.
      inversion H11. subst. inversion H5. subst. inversion H13. subst.
      + simpl in H21. exact H21.
      + congruence.
      + subst. simpl in H20. congruence.
Qed.

Example eq1_nos (e : Expression) (x : Var) (id id' : nat) env res eff eff':
 |env, (S id), e, eff | -e> | id', res, eff' |
<->
 |env, id, ELet x (EFun [] e) (EApp (EVar x) []), eff| -e> |id', res, eff'|.
Proof.
  split; intros.
  * eapply eval_let; auto.
    - apply eval_fun.
    - simpl. eapply eval_app with (vals := []) (var_list := []) (body := e) (ref := env)
                                    (ext := []) (eff := []) (eff2 := eff) (eff3 := eff') (ids := []); auto.
      + assert (get_value (insert_value env (inl x) (VClos env [] id [] e)) (inl x) 
                = inl (VClos env [] id [] e)). { apply get_value_here. }
        rewrite <- H0. apply eval_var. reflexivity.
      + intros. inversion H0.
      + simpl. unfold get_env. simpl. assumption.
  * inversion H; subst.
    - inversion H9. subst. unfold append_vars_to_env in H10. inversion H10; subst.
      + apply eq_sym, length_zero_iff_nil in H5. subst.
        apply eq_sym, length_zero_iff_nil in H6. subst.
        apply eq_sym, length_zero_iff_nil in H2. subst.
        inversion H3. subst. rewrite get_value_here in H5. inversion H5. subst.
        exact H16.
      + inversion H8. subst. rewrite get_value_here in H3. congruence.
      + inversion H2.
      + apply eq_sym, length_zero_iff_nil in H3. subst.
        apply eq_sym, length_zero_iff_nil in H4. subst.
        apply eq_sym, length_zero_iff_nil in H2. subst.
        inversion H5. subst. rewrite get_value_here in H3. inversion H3. subst.
        congruence.
      + apply eq_sym, length_zero_iff_nil in H3. subst.
        apply eq_sym, length_zero_iff_nil in H4. subst.
        apply eq_sym, length_zero_iff_nil in H2. subst.
        inversion H5. subst. rewrite get_value_here in H3. inversion H3. subst.
        simpl in H7. congruence.
    - inversion H9.
Qed.

Proposition plus_comm_basic_value {e1 e2 v : Value} (eff eff2 : SideEffectList) : 
  eval "+"%string [e1 ; e2] eff = (inl v, eff)
->
  eval "+"%string [e2; e1] eff2 = (inl v, eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_effect_changeable {v1 v2 : Value} (v' : Value + Exception) (eff eff2 : SideEffectList) :
  eval "+"%string [v1; v2] eff = (v', eff)
->
  eval "+"%string [v1; v2] eff2 = (v', eff2).
Proof.
  intros. simpl in *. case_eq v1; case_eq v2; intros; subst.
  all: try(inversion H; reflexivity).
  all: try(destruct l); try(inversion H; reflexivity).
  all: destruct l0; inversion H; auto.
Qed.

Example eq2_pbs_helper env id eff A B e1 e2 v1 v2 eff1 eff2 id1 id2 t:
  | env, id, e1, eff | -p> |id + id1, inl v1, eff ++ eff1| ->
  | env, id, e2, eff | -p> |id + id2, inl v2, eff ++ eff2| ->
  | insert_value env (inl B) v2, id + id2, e1, eff ++ eff2| -p> |id + id2 + id1, inl v1, eff ++ eff2 ++ eff1 | ->
  | insert_value env (inl A) v1, id + id1, e2, eff ++ eff1| -p> |id + id1 + id2, inl v2, eff ++ eff1 ++ eff2 | ->
  A <> B ->
  | env, id, 
      ELet B e2 (ELet A e1
        (ECall "+"%string [EVar A ; EVar B])),
      eff | -p> | id + id2 + id1, inl t, eff ++ eff2 ++ eff1|
<->
  | env, id, 
      ELet A e1 (ELet B e2
        (ECall "+"%string [EVar A ; EVar B])),
      eff| -p> | id + id1 + id2, inl t, eff ++ eff1 ++ eff2|.
Proof.
  split;
  intros.
  {
   inversion H4. subst.
  (* let deconstruction 2x *)
  pose (peval_expr_determinism _ _ _ _ _ _ _ H0 _ _ _ H14). destruct a. destruct H6. subst.
  inversion H15. subst. inversion H16. subst.
  pose (peval_expr_determinism _ _ _ _ _ _ _ H1 _ _ _ H17). destruct a. destruct H6. subst.
  inversion H18. subst. inversion H19. subst.
  (* call deconstruction *)
  inversion H9. subst. inversion H22. subst. unfold append_vars_to_env in *. rewrite get_value_here in *.
  inversion H23. subst. inversion H24. subst. unfold append_vars_to_env in *. rewrite get_value_there, get_value_here in *. 2-3: congruence.
  
  inversion H25. subst.
  inversion H20. subst.
  
  eapply peval_let.
  * exact H.
  * eapply peval_let_fin. eapply peval_let.
    - exact H2.
    - eapply peval_let_fin. eapply peval_call.
      + eapply peval_list_cons. eapply peval_var. simpl. rewrite get_value_there, get_value_here. reflexivity. congruence.
        simpl. eapply peval_list_cons. eapply peval_var. rewrite get_value_here. reflexivity.
        eapply peval_empty.
      + eapply peval_call_fin.
        simpl. apply plus_effect_changeable with (eff ++ eff2 ++ eff1). assumption.
 }
 
 (* This is boiler plate *)
 {
 intros. inversion H4. subst.
  (* let deconstruction 2x *)
  pose (peval_expr_determinism _ _ _ _ _ _ _ H _ _ _ H14). destruct a. destruct H6. subst.
  inversion H15. subst. inversion H16. subst.
  pose (peval_expr_determinism _ _ _ _ _ _ _ H2 _ _ _ H17). destruct a. destruct H6. subst.
  inversion H18. subst. inversion H19. subst.
  (* call deconstruction *)
  inversion H9. subst. inversion H22. subst. unfold append_vars_to_env in *. rewrite get_value_there, get_value_here in *. 2-3: congruence.
  inversion H23. subst. inversion H24. subst. unfold append_vars_to_env in *. rewrite get_value_here in *.
  
  inversion H25. subst.
  inversion H20. subst.
  
  eapply peval_let.
  * exact H0.
  * eapply peval_let_fin. eapply peval_let.
    - exact H1.
    - eapply peval_let_fin. eapply peval_call.
      + eapply peval_list_cons. eapply peval_var. simpl. rewrite get_value_here. reflexivity.
        simpl. eapply peval_list_cons. eapply peval_var. rewrite get_value_there, get_value_here. reflexivity. congruence.
        eapply peval_empty.
      + eapply peval_call_fin.
        simpl. apply plus_effect_changeable with (eff ++ eff1 ++ eff2). assumption.
 }
Qed.

Example eq2_nos_helper env id eff A B e1 e2 v1 v2 eff1 eff2 id1 id2 t:
  | env, id, e1, eff | -e> |id + id1, inl v1, eff ++ eff1| ->
  | env, id, e2, eff | -e> |id + id2, inl v2, eff ++ eff2| ->
  | insert_value env (inl B) v2, id + id2, e1, eff ++ eff2| -e> |id + id2 + id1, inl v1, eff ++ eff2 ++ eff1 | ->
  | insert_value env (inl A) v1, id + id1, e2, eff ++ eff1| -e> |id + id1 + id2, inl v2, eff ++ eff1 ++ eff2 | ->
  A <> B ->
  | env, id, 
      ELet B e2 (ELet A e1
        (ECall "+"%string [EVar A ; EVar B])),
      eff | -e> | id + id2 + id1, inl t, eff ++ eff2 ++ eff1|
<->
  | env, id, 
      ELet A e1 (ELet B e2
        (ECall "+"%string [EVar A ; EVar B])),
      eff| -e> | id + id1 + id2, inl t, eff ++ eff1 ++ eff2|.
Proof.
  split; intros.
  {
    inversion H4. subst.
    inversion H15. subst.
    pose (nos_determinism H14 _ _ _ H0). destruct a. destruct H6. inversion H5. subst.
    simpl in H16.
    pose (nos_determinism H16 _ _ _ H1). destruct a. destruct H7. inversion H6. subst.
    inversion H17. subst.
    pose (EC1 := element_exist 1 _ H9).
    pose (EC2 := element_exist 1 _ H10).
    pose (EC3 := element_exist 1 _ H11).
    inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
    inversion H7. inversion H8. inversion H13. subst. 
    inversion H9. inversion H10. inversion H11.
    pose (EC1' := element_exist 0 _ H20).
    pose (EC2' := element_exist 0 _ H21).
    pose (EC3' := element_exist 0 _ H22).
    inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
    inversion H18. inversion H23. inversion H25. subst.
    inversion H20. inversion H21. inversion H22.
    apply eq_sym, length_zero_iff_nil in H27.
    apply eq_sym, length_zero_iff_nil in H28.
    apply eq_sym, length_zero_iff_nil in H29. subst.
     
    pose (P1' := H12 0 Nat.lt_0_2).
    pose (P2' := H12 1 Nat.lt_1_2).
    inversion P1'. inversion P2'. simpl in *. subst.
     
    rewrite get_value_there in H37. 2: congruence.
    rewrite get_value_here in H29. inversion H29.
    rewrite get_value_here in H37. inversion H37. subst.
    
    eapply eval_let.
    * exact H.
    * eapply eval_let.
      - exact H2.
      - eapply eval_call with (vals := [v1; v2]) 
                              (eff := [eff ++ eff1 ++ eff2; eff ++ eff1 ++ eff2]) 
                              (ids := [id + id1 + id2; id + id1 + id2]); auto.
        + intros. inversion H24. 2: inversion H27.
          ** eapply eval_var. simpl. rewrite get_value_here. auto.
          ** eapply eval_var. simpl. rewrite get_value_there, get_value_here. auto. congruence.
          ** inversion H30.
        + simpl. apply plus_effect_changeable with (eff ++ eff2 ++ eff1). assumption.
  }
  {
    inversion H4. subst.
    inversion H15. subst.
    pose (nos_determinism H14 _ _ _ H). destruct a. destruct H6. inversion H5. subst.
    simpl in H16.
    pose (nos_determinism H16 _ _ _ H2). destruct a. destruct H7. inversion H6. subst.
    inversion H17. subst.
    pose (EC1 := element_exist 1 _ H9).
    pose (EC2 := element_exist 1 _ H10).
    pose (EC3 := element_exist 1 _ H11).
    inversion EC1 as [x'']. inversion EC2 as [eff1'']. inversion EC3 as [id1''].
    inversion H7. inversion H8. inversion H13. subst. 
    inversion H9. inversion H10. inversion H11.
    pose (EC1' := element_exist 0 _ H20).
    pose (EC2' := element_exist 0 _ H21).
    pose (EC3' := element_exist 0 _ H22).
    inversion EC1' as [x0'']. inversion EC2' as [eff2'']. inversion EC3' as [id2''].
    inversion H18. inversion H23. inversion H25. subst.
    inversion H20. inversion H21. inversion H22.
    apply eq_sym, length_zero_iff_nil in H27.
    apply eq_sym, length_zero_iff_nil in H28.
    apply eq_sym, length_zero_iff_nil in H29. subst.
     
    pose (P1' := H12 0 Nat.lt_0_2).
    pose (P2' := H12 1 Nat.lt_1_2).
    inversion P1'. inversion P2'. simpl in *. subst.
     
    rewrite get_value_there in H29. 2: congruence.
    rewrite get_value_here in H37. inversion H37.
    rewrite get_value_here in H29. inversion H29. subst.
    
    eapply eval_let.
    * exact H0.
    * eapply eval_let.
      - exact H1.
      - eapply eval_call with (vals := [v1; v2]) 
                              (eff := [eff ++ eff2 ++ eff1; eff ++ eff2 ++ eff1]) 
                              (ids := [id + id2 + id1; id + id2 + id1]); auto.
        + intros. inversion H24. 2: inversion H27.
          ** eapply eval_var. simpl. rewrite get_value_there, get_value_here. auto. congruence.
          ** eapply eval_var. simpl. rewrite get_value_here. auto.
          ** inversion H30.
        + simpl. apply plus_effect_changeable with (eff ++ eff1 ++ eff2). assumption.
  }
Qed.

Lemma pbos_list_correctness_helper :
forall {l env id0 eff0 id' eff' l0} v vals,
  | env, id0, AList l (inl vals), eff0 | -l> | id', inl l0, eff' |
->
  | env, id0, AList l (inl (v :: vals)), eff0 | -l> | id', inl (v :: l0), eff' |.
Proof.
  induction l; intros; inversion H; subst.
  * eapply peval_empty.
  * destruct res.
    - simpl in H10. eapply peval_list_cons.
      exact H9. simpl. pose(IHl _ _ _ _ _ _ v (vals ++ [v0]) H10).
      exact p.
    - inversion H10.
Qed.


Lemma fbos_pbos_list_correcness :
forall l clock env id eff id' l' eff',
  eval_elems (eval_fbos_expr clock) env id l eff = LResult id' (inl l') eff'
->
(forall (env : Environment) (id : nat) (exp : Expression) 
          (eff : SideEffectList) (id' : nat) (res : Value + Exception)
          (eff' : SideEffectList),
        eval_fbos_expr clock env id exp eff = Result id' res eff' ->
        | env, id, exp, eff | -p> | id', res, eff' |)
->
  | env, id, AList l (inl []), eff | -l> |id', inl l', eff'|.
Proof.
  induction l; intros.
  * simpl in H. inversion H. apply peval_empty.
  * simpl in H. case_eq (eval_fbos_expr clock env id a eff); intros; rewrite H1 in H.
    destruct res.
    - case_eq (eval_elems (eval_fbos_expr clock) env id0 l eff0); intros; rewrite H2 in H.
      destruct res.
      + inversion H. subst.
        epose (P := IHl _ _ _ _ _ _ _ H2 _).
        apply H0 in H1.
        eapply peval_list_cons. exact H1. simpl.
        pose (P1 := pbos_list_correctness_helper v [] P). exact P1.
        Unshelve.
        intros. apply H0. auto.
      + congruence.
      + congruence.
      + congruence.
    - congruence.
    - congruence.
    - congruence.
Qed.

Lemma pbos_list_correctness_helper_ex :
forall {l env id0 eff0 id' eff' ex} v vals,
  | env, id0, AList l (inl vals), eff0 | -l> | id', inr ex, eff' |
->
  | env, id0, AList l (inl (v :: vals)), eff0 | -l> | id', inr ex, eff' |.
Proof.
  induction l; intros; inversion H; subst.
  * destruct res.
    - simpl in H10. eapply peval_list_cons.
      exact H9. simpl. pose(IHl _ _ _ _ _ _ v (vals ++ [v0]) H10).
      exact p.
    - simpl in H10. eapply peval_list_cons.
      exact H9. simpl. inversion H10. subst. eapply peval_list_exc.
Qed.

Lemma fbos_pbos_list_correcness_ex :
forall l clock env id eff id' eff' ex,
  eval_elems (eval_fbos_expr clock) env id l eff = LResult id' (inr ex) eff'
->
(forall (env : Environment) (id : nat) (exp : Expression) 
          (eff : SideEffectList) (id' : nat) (res : Value + Exception)
          (eff' : SideEffectList),
        eval_fbos_expr clock env id exp eff = Result id' res eff' ->
        | env, id, exp, eff | -p> | id', res, eff' |)
->
  | env, id, AList l (inl []), eff | -l> |id', inr ex, eff'|.
Proof.
  induction l; intros.
  * simpl in H. inversion H.
  * simpl in H. case_eq (eval_fbos_expr clock env id a eff); intros; rewrite H1 in H.
    destruct res.
    - case_eq (eval_elems (eval_fbos_expr clock) env id0 l eff0); intros; rewrite H2 in H.
      destruct res.
      + congruence.
      + inversion H. subst.
        epose (P := IHl _ _ _ _ _ _ _ H2 _).
        apply H0 in H1.
        eapply peval_list_cons. exact H1. simpl.
        pose (P1 := pbos_list_correctness_helper_ex v [] P). exact P1.
        Unshelve.
        intros. apply H0. auto.
      + congruence.
      + congruence.
    - inversion H. subst. eapply H0 in H1. eapply peval_list_cons.
      exact H1. simpl. apply peval_list_exc.
    - congruence.
    - congruence.
Qed.


Theorem fbos_pbos_correctness :
forall clock env id exp eff id' res eff',
  eval_fbos_expr clock env id exp eff = Result id' res eff'
->
  | env, id, exp, eff | -p> | id', res, eff' |.
Proof.
  induction clock; intros.
  * inversion H.
  * destruct exp.
    - simpl in H. inversion H. subst. apply peval_lit.
    - simpl in H. inversion H. subst. apply peval_var. auto.
    - simpl in H. inversion H. subst. apply peval_funid. auto.
    - simpl in H. inversion H. subst. apply peval_fun.
    - simpl in H. case_eq (eval_elems (eval_fbos_expr clock) env id l eff); intros; rewrite H0 in H. destruct res0.
      + apply fbos_pbos_list_correcness in H0. 2: auto.
        inversion H. subst. eapply peval_call. exact H0.
        eapply peval_call_fin. rewrite <- surjective_pairing. auto.
      + apply fbos_pbos_list_correcness_ex in H0. 2: auto.
        eapply peval_call. exact H0. inversion H. subst.
        eapply peval_call_exc.
      + congruence.
      + congruence.
    - simpl in H.
      case_eq (eval_fbos_expr clock env id exp eff); intros; rewrite H0 in H.
      destruct res0.
      + case_eq (eval_elems (eval_fbos_expr clock) env id0 l eff0); intros; rewrite H1 in H.
        destruct res0.
        ** apply IHclock in H0.
           apply fbos_pbos_list_correcness in H1. 2: auto.
           eapply peval_app. exact H0.
           eapply peval_app1_fin. exact H1.
           destruct v.
           -- inversion H. subst. eapply peval_app2_exc1. congruence.
           -- case_eq ((Datatypes.length vl =? Datatypes.length l0)%nat); intros; rewrite H2 in H.
              ++ rewrite Nat.eqb_eq in H2.
                 eapply peval_app2_fin. auto. apply IHclock in H. auto.
              ++ rewrite Nat.eqb_neq in H2. inversion H. subst.
                 eapply peval_app2_exc2. auto.
        ** apply IHclock in H0.
           apply fbos_pbos_list_correcness_ex in H1. 2: auto.
           inversion H. subst.
           eapply peval_app. exact H0.
           eapply peval_app1_fin. exact H1.
           eapply peval_app2_exc.
        ** congruence.
        ** congruence.
      + inversion H. subst. eapply peval_app.
        apply IHclock in H0. exact H0.
        eapply peval_app1_exc.
      + congruence.
      + congruence.
    - simpl in H. case_eq (eval_fbos_expr clock env id exp1 eff); intros; rewrite H0 in H.
      destruct res0.
      + apply IHclock in H. apply IHclock in H0.
        eapply peval_let. exact H0.
        eapply peval_let_fin. exact H.
      + apply IHclock in H0. inversion H; subst.
        eapply peval_let. exact H0. eapply peval_let_exc.
      + congruence.
      + congruence.
    - simpl in H. apply IHclock in H. eapply peval_letrec. auto.
    - simpl in H. case_eq (eval_fbos_expr clock env id exp1 eff); intros; rewrite H0 in H.
      destruct res0.
      + apply IHclock in H. apply IHclock in H0.
        eapply peval_try. exact H0.
        eapply peval_try1_fin. exact H.
      + apply IHclock in H0. apply IHclock in H.
        eapply peval_try. exact H0. eapply peval_try1_exc.
        exact H.
      + congruence.
      + congruence.
Qed.

Lemma ppbos_list_soundness_helper :
forall {l env id0 eff0 id' eff' l0 n} v vals,
  | env, id0, AList l (inl (v::vals)), eff0, n | -ll> | id', inl l0, eff' |
->
  | env, id0, AList l (inl vals), eff0, n | -ll> | id', inl (tail l0), eff' |.
Proof.
  induction l; intros; inversion H; subst.
  * eapply ppeval_empty.
  * destruct res.
    - simpl in H10. eapply ppeval_list_cons.
      exact H10. simpl. pose(IHl _ _ _ _ _ _ _ v (vals ++ [v0]) H11).
      exact p.
    - inversion H11.
Qed.

Lemma ppbos_list_soundness_helper_ex :
forall {l env id0 eff0 id' eff' ex n} v vals,
  | env, id0, AList l (inl (v::vals)), eff0, n | -ll> | id', inr ex, eff' |
->
  | env, id0, AList l (inl vals), eff0, n | -ll> | id', inr ex, eff' |.
Proof.
  induction l; intros; inversion H; subst.
  * destruct res.
    - simpl in H10. eapply ppeval_list_cons.
      exact H10. simpl. pose(IHl _ _ _ _ _ _ _ v (vals ++ [v0]) H11).
      exact p.
    - inversion H11. subst. eapply ppeval_list_cons. exact H10.
      exact H11.
Qed.

Theorem fst_ppbos_helper:
forall params n env id v vals eff id' l eff',
| env, id, AList params (inl (v::vals)), eff, S n | -ll> | id', inl l, eff' |
->
head l = Some v.
Proof.
  induction params; intros.
  * inversion H. subst. simpl. auto.
  * inversion H. subst. destruct res.
    - simpl in H11. apply ppeval_list_increase with (n1 := S n) in H11. 2: lia.
      pose (IHparams _ _ _ _ _ _ _ _ _ H11). auto.
    - inversion H11.
Qed.

Theorem ppbos_soundess_list :
forall params n0 env id eff id' res eff',
  | env, id, AList params (inl []), eff, n0 | -ll> | id', res, eff' |
->
(forall (env : Environment) (id : nat) (exp : Expression) (eff : SideEffectList)
        (id' : nat) (res : Value + Exception) (eff' : SideEffectList),
      | env, id, exp, eff, n0 | -pp> | id', res, eff' | ->
      exists clock : nat, eval_fbos_expr clock env id exp eff = Result id' res eff')
->
  exists clock, eval_elems (eval_fbos_expr clock) env id params eff = LResult id' res eff'.
Proof.
  induction params; intros.
  * inversion H. subst. exists 1. simpl. auto.
  * inversion H. subst. destruct res0.
    - eapply ppeval_expr_increase in H11.
      pose (H0 _ _ _ _ _ _ _ H11). destruct e.
      simpl in H12.
      destruct res.
      + apply ppeval_list_increase with (n1 := S n) in H12. 2: lia.
        pose (ppbos_list_soundness_helper v [] H12).
        epose (IHparams _ _ _ _ id' _ eff' p H0). destruct e.
        exists (x + x0). simpl. eapply bigger_clock in H1. rewrite H1.
        eapply bigger_list_clock in H2. rewrite H2.
        clear p.
        apply fst_ppbos_helper in H12.
        Search hd_error.
        destruct l. inversion H12.
        simpl. simpl in H12. inversion H12. auto. lia. lia.
      + pose (ppbos_list_soundness_helper_ex _ _ H12).
        apply ppeval_list_increase with (n1 := S n) in p. 2: lia.
        epose (IHparams _ _ _ _ id' _ eff' p H0). destruct e0.
        exists (x + x0). simpl.
        eapply bigger_clock in H1. rewrite H1.
        eapply bigger_list_clock in H2. rewrite H2.
        auto. lia. lia.
      + lia.
    - inversion H12. subst.
      eapply ppeval_expr_increase in H11.
      pose (H0 _ _ _ _ _ _ _ H11). 2: lia. destruct e0.
      exists (x). simpl. rewrite H1. auto.
Qed.

Theorem fbos_ppbos_soundness :
(forall n env id exp eff id' res eff',
  | env, id, exp, eff, n | -pp> | id', res, eff' |
->
  exists clock, eval_fbos_expr clock env id exp eff = Result id' res eff').
Proof.
  induction n; intros; inversion H; subst.
  1-4: exists 1; auto.
  * apply IHn in H1.
    inversion H6; subst.
    - destruct H1. exists (S x). simpl. rewrite H0. auto.
    - eapply ppeval_expr_increase in H12. apply IHn in H12. 2: lia.
      destruct H1, H12. exists (S (x + x0)). simpl.
      eapply bigger_clock with (clock' := x + x0) in H0.
      eapply bigger_clock with (clock' := x + x0) in H1.
      rewrite H0. auto. lia. lia.
  * apply IHn in H1.
    inversion H6; subst.
    - destruct H1. exists (S x). simpl. rewrite H0. auto.
    - apply ppbos_soundess_list in H5.
      2: { intros. apply IHn. eapply ppeval_expr_increase in H0. exact H0. lia. }
      destruct H1, H5.
      inversion H12; subst.
      + rewrite <- Nat.eqb_eq in H7.
        eapply ppeval_expr_increase in H14.
        apply IHn in H14. destruct H14. exists (S (x + x0 + x1)).
        simpl.
        eapply bigger_clock in H0. eapply bigger_clock in H2. eapply bigger_list_clock in H1.
        rewrite H0, H1, H2. rewrite H7. auto. all: lia.
      + exists (S (x + x0)).
        eapply bigger_clock in H0. eapply bigger_list_clock in H1.
        simpl. rewrite H0, H1. destruct v.
        ** congruence.
        ** congruence.
        ** lia.
        ** lia.
      + exists (S (x + x0)). simpl.
        eapply bigger_clock in H0. eapply bigger_list_clock in H1.
        rewrite H0, H1. rewrite <- Nat.eqb_neq in H13. rewrite H13. auto. lia. lia.
      + exists (S (x + x0)). simpl.
        eapply bigger_clock in H0. eapply bigger_list_clock in H1.
        rewrite H0, H1. auto. lia. lia.
  * apply ppbos_soundess_list in H1. 2: auto. destruct H1.
    inversion H6; subst.
    - exists (S x). simpl. rewrite H0. rewrite surjective_pairing in H11 at 1.
      inversion H11. auto.
    - exists (S x). simpl. rewrite H0. auto.
  * apply IHn in H1.
    inversion H6; subst.
    - eapply ppeval_expr_increase in H14. apply IHn in H14. destruct H1, H14.
      exists (S (x + x0)). simpl. eapply bigger_clock in H0.
      eapply bigger_clock in H1. rewrite H0, H1. auto.
      all: lia.
    - eapply ppeval_expr_increase in H14. apply IHn in H14. destruct H1, H14.
      exists (S (x + x0)). simpl. eapply bigger_clock in H0.
      eapply bigger_clock in H1. rewrite H0, H1. auto.
      all: lia.
  * apply IHn in H5. destruct H5. exists (S x). simpl. auto.
Qed.

Theorem fbos_pbos_soundness :
(forall env id exp eff id' res eff',
  | env, id, exp, eff | -p> | id', res, eff' |
->
  exists clock, eval_fbos_expr clock env id exp eff = Result id' res eff').
Proof.
  intros. apply peval_ppeval in H. destruct H.
  eapply fbos_ppbos_soundness. exact H.
Qed.


Theorem nos_pbos_soundness :
  forall env id exp eff id' res eff',
  | env, id, exp, eff | -e> | id', res, eff' |
->
  | env, id, exp, eff | -p> | id', res, eff' |.
Proof.
  intros.
  pose (fbos_sound _ _ _ _ _ _ _ H). destruct e.
  eapply fbos_pbos_correctness. exact H0.
Qed.

Theorem nos_pbos_correctness :
  forall env id exp eff id' res eff',
  | env, id, exp, eff | -p> | id', res, eff' |
->
  | env, id, exp, eff | -e> | id', res, eff' |.
Proof.
  intros.
  pose (fbos_pbos_soundness _ _ _ _ _ _ _ H). destruct e.
  eapply fbos_correct. exact H0.
Qed.