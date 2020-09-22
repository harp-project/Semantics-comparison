Require Export CE_FBOS.
Require Export CE_NOS.
Require Export CE_PBOS.

Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.

Section indhyp.

Axiom Expression_ind_2 :
forall P : Expression -> Prop,
       P ENil ->
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

End indhyp.

Theorem clock_list_increase :
forall l env id eff id' res eff' clock,
(forall (env : Environment) (id : nat) (exp : Expression) 
            (eff : SideEffectList) (id' : nat) (res : Value + Exception)
            (eff' : SideEffectList),
          eval_fbos_expr env id exp eff clock = Result id' res eff' ->
          eval_fbos_expr env id exp eff (S clock) = Result id' res eff') ->
(fix eval_list
   (env : Environment) (id : nat) (exps : list Expression) 
   (eff : SideEffectList) {struct exps} : ResultListType :=
   match exps with
   | nil => LResult id (inl nil) eff
   | x :: xs =>
       match eval_fbos_expr env id x eff clock with
       | Result id' (inl v) eff' =>
           match eval_list env id' xs eff' with
           | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
           | LResult id'' (inr _) _ => eval_list env id' xs eff'
           | _ => eval_list env id' xs eff'
           end
       | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
       | Timeout => LTimeout
       | Failure => LFailure
       end
   end) env id l eff = LResult id' res eff' ->
(fix eval_list
   (env : Environment) (id : nat) (exps : list Expression) 
   (eff : SideEffectList) {struct exps} : ResultListType :=
   match exps with
   | nil => LResult id (inl nil) eff
   | x :: xs =>
       match eval_fbos_expr env id x eff clock with
       | Result id' (inl v) eff' =>
           match eval_list env id' xs eff' with
           | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
           | LResult id'' (inr _) _ => eval_list env id' xs eff'
           | _ => eval_list env id' xs eff'
           end
       | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
       | Timeout => LTimeout
       | Failure => LFailure
       end
   end) env id l eff =
(fix eval_list
   (env : Environment) (id : nat) (exps : list Expression) 
   (eff : SideEffectList) {struct exps} : ResultListType :=
   match exps with
   | nil => LResult id (inl nil) eff
   | x :: xs =>
       match eval_fbos_expr env id x eff (S clock) with
       | Result id' (inl v) eff' =>
           match eval_list env id' xs eff' with
           | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
           | LResult id'' (inr _) _ => eval_list env id' xs eff'
           | _ => eval_list env id' xs eff'
           end
       | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
       | Timeout => LTimeout
       | Failure => LFailure
       end
   end) env id l eff.
Proof.
  induction l; intros.
  * auto.
  * case_eq (eval_fbos_expr env id a eff clock); intros.
    - pose (H _ _ _ _ _ _ _ H1).
      rewrite H1 in H0.
      rewrite e. case_eq res0; intros; subst.
      + (* pose (IHl env id0 eff0 id' res eff' clock H). *)
        case_eq ((fix eval_list
          (env : Environment) (id : nat) (exps : list Expression) 
          (eff : SideEffectList) {struct exps} : ResultListType :=
          match exps with
          | nil => LResult id (inl nil) eff
          | x :: xs =>
              match eval_fbos_expr env id x eff clock with
              | Result id' (inl v) eff' =>
                  match eval_list env id' xs eff' with
                  | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                  | LResult id'' (inr _) _ => eval_list env id' xs eff'
                  | _ => eval_list env id' xs eff'
                  end
              | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
              | Timeout => LTimeout
              | Failure => LFailure
              end
          end) env id0 l eff0); intros.
       ** case_eq res0; intros.
         -- inversion H0. subst.
            pose (IHl env id0 eff0 id1 (inl l0) eff1 clock H H2).
            rewrite <- e0. rewrite H2. auto.
         -- inversion H0. subst.
            pose (IHl env id0 eff0 id1 _ eff1 clock H H2).
            rewrite <- e1. rewrite H2. auto.
       ** rewrite H2 in H0. discriminate.
       ** rewrite H2 in H0. discriminate.
     + auto.
   - rewrite H1 in H0. discriminate.
   - rewrite H1 in H0. discriminate.
Qed.

Theorem clock_increase :
  forall clock env id exp eff id' res eff',
  eval_fbos_expr env id exp eff clock = Result id' res eff'
->
  eval_fbos_expr env id exp eff (S clock) = Result id' res eff'.
Proof.
  induction clock; intros; subst.
  * simpl in H. inversion H.
  * destruct exp.
    - simpl in *. inversion H. auto.
    - simpl in *. inversion H. auto.
    - simpl in *. inversion H. auto.
    - simpl in *. inversion H. auto.
    - simpl in *. inversion H. auto.
    - simpl in H. 
    remember ((fix eval_list
          (env : Environment) (id : nat) (exps : list Expression) 
          (eff : SideEffectList) {struct exps} : ResultListType :=
          match exps with
          | nil => LResult id (inl nil) eff
          | x :: xs =>
              match eval_fbos_expr env id x eff clock with
              | Result id' (inl v) eff' =>
                  match eval_list env id' xs eff' with
                  | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                  | LResult id'' (inr _) _ => eval_list env id' xs eff'
                  | _ => eval_list env id' xs eff'
                  end
              | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
              | Timeout => LTimeout
              | Failure => LFailure
              end
          end) env id l eff) as result.
    destruct result. 2-3: discriminate. symmetry in Heqresult.
    assert ((fix eval_list
               (env : Environment) (id : nat) (exps : list Expression) 
               (eff : SideEffectList) {struct exps} : ResultListType :=
               match exps with
               | nil => LResult id (inl nil) eff
               | x :: xs =>
                   match eval_fbos_expr env id x eff clock with
                   | Result id' (inl v) eff' =>
                       match eval_list env id' xs eff' with
                       | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                       | LResult id'' (inr _) _ => eval_list env id' xs eff'
                       | _ => eval_list env id' xs eff'
                       end
                   | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
                   | Timeout => LTimeout
                   | Failure => LFailure
                   end
               end) env id l eff = LResult id0 res0 eff0). { auto. }
    pose (clock_list_increase _ _ _ _ _ _ _ _ IHclock Heqresult). rewrite e in H0.
    clear e. clear Heqresult.
    remember (S clock) as cl. simpl. rewrite H0. assumption.
  - simpl in H. case_eq (eval_fbos_expr env id exp eff clock); intros. destruct res0.
    + rewrite H0 in H. remember ((fix eval_list
         (env : Environment) (id : nat) (exps : list Expression) (eff : SideEffectList)
         {struct exps} : ResultListType :=
         match exps with
         | [] => LResult id (inl []) eff
         | x :: xs =>
             match eval_fbos_expr env id x eff clock with
             | Result id' (inl v) eff' =>
                 match eval_list env id' xs eff' with
                 | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                 | LResult id'' (inr _) _ => eval_list env id' xs eff'
                 | _ => eval_list env id' xs eff'
                 end
             | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
             | Timeout => LTimeout
             | Failure => LFailure
             end
         end) env id0 l eff0) as result.
         destruct result. 2-3: discriminate. symmetry in Heqresult.
         remember (S clock) as cl. simpl. apply IHclock in H0. rewrite H0.
         rewrite Heqcl in IHclock.
         pose (clock_list_increase _ _ _ _ _ _ _ _ IHclock Heqresult).
         assert ((fix eval_list
               (env : Environment) (id : nat) (exps : list Expression) 
               (eff : SideEffectList) {struct exps} : ResultListType :=
               match exps with
               | [] => LResult id (inl []) eff
               | x :: xs =>
                   match eval_fbos_expr env id x eff clock with
                   | Result id' (inl v) eff' =>
                       match eval_list env id' xs eff' with
                       | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                       | LResult id'' (inr _) _ => eval_list env id' xs eff'
                       | _ => eval_list env id' xs eff'
                       end
                   | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
                   | Timeout => LTimeout
                   | Failure => LFailure
                   end
               end) env id0 l eff0 = LResult id1 res0 eff1). { auto. }
         rewrite e in H1. rewrite <- Heqcl in H1. rewrite H1.
         clear H1. clear dependent Heqresult. destruct res0.
         ** destruct v; auto.
            destruct ((Datatypes.length l0 =? Datatypes.length vl)%nat); auto.
            apply IHclock in H. rewrite Heqcl. exact H.
         ** inversion H. subst. auto.
    + rewrite H0 in H. inversion H. subst. remember (S clock) as cl. simpl.
      apply IHclock in H0.
      rewrite H0. reflexivity.
    + rewrite H0 in H. discriminate.
    + rewrite H0 in H. discriminate.
  - simpl in H. case_eq (eval_fbos_expr env id exp1 eff clock); intros. destruct res0.
    + rewrite H0 in H. remember (S clock) as cl. simpl.
      case_eq (eval_fbos_expr env id exp1 eff cl); intros. destruct res0.
      ** apply IHclock in H0. rewrite H0 in H1. inversion H1. subst. apply IHclock in H. assumption.
      ** apply IHclock in H0. rewrite H0 in H1. inversion H1.
      ** apply IHclock in H0. congruence.
      ** apply IHclock in H0. congruence.
    + rewrite H0 in H. inversion H. subst. remember (S clock) as cl.
      apply IHclock in H0. simpl. rewrite H0. auto.
    + rewrite H0 in H. congruence.
    + rewrite H0 in H. congruence.
  - simpl in H. remember (S clock) as cl. simpl. apply IHclock in H. assumption.
  - simpl in H. case_eq (eval_fbos_expr env id exp1 eff clock); intros. destruct res0.
    + rewrite H0 in H. remember (S clock) as cl. simpl.
      case_eq (eval_fbos_expr env id exp1 eff cl); intros. destruct res0.
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
  eval_fbos_expr env id exp eff clock = Result id' res eff'
->
  eval_fbos_expr env id exp eff clock' = Result id' res eff'.
Proof.
  intros. induction H.
  * assumption. 
  * apply clock_increase. auto.
Qed.

(* Theorem restrict env l a :
(forall i : nat,
    i < Datatypes.length (a :: l) ->
    forall (id : nat) (eff : SideEffectList) (id' : nat) (res : Value + Exception)
      (eff' : SideEffectList),
    | env, id, nth i (a :: l) ErrorExp, eff | -e> | id', res, eff' | ->
    exists clock : nat,
      eval_fbos_expr env id (nth i (a :: l) ErrorExp) eff clock = Result id' res eff')
->
forall i : nat,
    i < Datatypes.length l ->
    forall (id : nat) (eff : SideEffectList) (id' : nat) (res : Value + Exception)
      (eff' : SideEffectList),
    | env, id, nth i l ErrorExp, eff | -e> | id', res, eff' | ->
    exists clock : nat,
      eval_fbos_expr env id (nth i l ErrorExp) eff clock = Result id' res eff'.
Proof.
  intros.
  assert (S i < Datatypes.length (a :: l)) as A1.
  { simpl. lia. } pose (E := H (S i) A1). 
  simpl in E. simpl. apply E. assumption.
Qed.

Theorem restrict_helper env l a id id' eff' v' eff x0 x x1 n :
(forall i : nat,
     i < S n ->
     | env, nth_def (id' :: x0) id 0 i, nth i (a :: l) ErrorExp,
     nth_def (eff' :: x1) eff [] i | -e> | nth_def (id' :: x0) id 0 (S i),
     inl (nth i (v' :: x) ErrorValue), nth_def (eff' :: x1) eff [] (S i) |)
->
forall i : nat,
     i < n ->
     | env, nth_def x0 id' 0 i, nth i l ErrorExp,
     nth_def x1 eff' [] i | -e> | nth_def x0 id' 0 (S i),
     inl (nth i x ErrorValue), nth_def x1 eff' [] (S i) |.
Proof.
  intros.
  assert (S i < S n) as A1.
  { simpl. lia. } pose (E := H (S i) A1).
  simpl in E. simpl. unfold nth_def. exact E.
Qed.

Theorem bigger_clock_list env x3 clock' l id' res eff' id1 eff1:
(fix eval_list
        (env0 : Environment) (id0 : nat) (exps : list Expression) 
        (eff1 : SideEffectList) {struct exps} : ResultListType :=
        match exps with
        | [] => LResult id0 (inl []) eff1
        | x :: xs =>
            match eval_fbos_expr env0 id0 x eff1 x3 with
            | Result id' (inl v) eff' =>
                match eval_list env0 id' xs eff' with
                | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                | LResult id'' (inr _) _ => eval_list env0 id' xs eff'
                | _ => eval_list env0 id' xs eff'
                end
            | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
            | Timeout => LTimeout
            | Failure => LFailure
            end
        end) env id' l eff' = LResult id1 res eff1 ->
  x3 <= clock'
->
(fix eval_list
        (env0 : Environment) (id0 : nat) (exps : list Expression) 
        (eff1 : SideEffectList) {struct exps} : ResultListType :=
        match exps with
        | [] => LResult id0 (inl []) eff1
        | x :: xs =>
            match eval_fbos_expr env0 id0 x eff1 clock' with
            | Result id' (inl v) eff' =>
                match eval_list env0 id' xs eff' with
                | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                | LResult id'' (inr _) _ => eval_list env0 id' xs eff'
                | _ => eval_list env0 id' xs eff'
                end
            | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
            | Timeout => LTimeout
            | Failure => LFailure
            end
        end) env id' l eff' = LResult id1 res eff1.
Proof.
  intros. induction H0.
  * subst. auto.
  * intros.
    assert ((fix eval_list
       (env0 : Environment) (id0 : nat) (exps : list Expression) 
       (eff1 : SideEffectList) {struct exps} : ResultListType :=
       match exps with
       | [] => LResult id0 (inl []) eff1
       | x :: xs =>
           match eval_fbos_expr env0 id0 x eff1 m with
           | Result id' (inl v) eff' =>
               match eval_list env0 id' xs eff' with
               | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
               | LResult id'' (inr _) _ => eval_list env0 id' xs eff'
               | _ => eval_list env0 id' xs eff'
               end
           | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
           | Timeout => LTimeout
           | Failure => LFailure
           end
       end) env id' l eff' = LResult id1 res eff1).
       { auto. }
    apply clock_list_increase in IHle. rewrite IHle in H1. assumption.
    - intros. apply clock_increase. assumption.
Qed.

Theorem list_sound :
  forall l env ids eff id eff0 vals,
(forall i : nat,
    i < Datatypes.length l ->
    forall (id : nat) (eff : SideEffectList) (id' : nat) (res : Value + Exception)
      (eff' : SideEffectList),
    | env, id, nth i l ErrorExp, eff | -e> | id', res, eff' | ->
    exists clock : nat, eval_fbos_expr env id (nth i l ErrorExp) eff clock = Result id' res eff')
->
(forall i : nat,
     i < Datatypes.length l ->
     | env, nth_def ids id 0 i, nth i l ErrorExp, nth_def eff0 eff nil i | -e>
     | nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff0 eff nil (S i) |)
->
Datatypes.length l = Datatypes.length vals ->
Datatypes.length l = Datatypes.length ids ->
Datatypes.length l = Datatypes.length eff0 ->
exists clock, (fix eval_list
     (env0 : Environment) (id0 : nat) (exps : list Expression) (eff1 : SideEffectList)
     {struct exps} : ResultListType :=
     match exps with
     | nil => LResult id0 (inl nil) eff1
     | x :: xs =>
         match eval_fbos_expr env0 id0 x eff1 clock with
         | Result id' (inl v) eff' =>
             match eval_list env0 id' xs eff' with
             | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
             | LResult id'' (inr _) _ => eval_list env0 id' xs eff'
             | _ => eval_list env0 id' xs eff'
             end
         | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
         | Timeout => LTimeout
         | Failure => LFailure
         end
     end) env id l eff = LResult (last ids id) (inl vals) (last eff0 eff).
Proof.
  induction l.
  * intros. apply eq_sym, length_zero_iff_nil in H1.
    apply eq_sym, length_zero_iff_nil in H2. apply eq_sym, length_zero_iff_nil in H3.
    subst. exists 0. auto.
  * intros.
    pose (EE1 := element_exist _ _ H1).
    pose (EE2 := element_exist _ _ H2).
    pose (EE3 := element_exist _ _ H3).
    inversion EE1 as [v']. inversion EE2 as [id']. inversion EE3 as [eff'].
    inversion H4. inversion H5. inversion H6. subst.
    clear EE1. clear EE2. clear EE3. clear H4. clear H5. clear H6.
    assert (0 < Datatypes.length (a :: l)). { simpl. lia. }
    pose (P1 := H0 0 H4).
    pose (P2 := H 0 H4 _ _ _ _ _ P1). inversion P2. simpl in H5.
    inversion H1. inversion H2. inversion H3.
    pose (IH := IHl env x0 eff' id' x1 x (restrict env l a H) 
                 (restrict_helper _ _ _ _ _ _ _ _ _ _ _ (length l) H0) H7 H8 H9). inversion IH.
    clear IH. clear IHl.
    exists (x2 + x3).
    apply bigger_clock with (clock' := x2 + x3) in H5. 2: lia.
    rewrite H5.
    apply bigger_clock_list with (clock' := x2 + x3) in H6.
    rewrite H6.
    rewrite last_element_equal with (def2 := eff).
    rewrite last_element_equal with (def2 := id). auto.
    - lia.
Qed.

Theorem list_exception_sound :
  forall l env ids eff id eff0 vals ex id' eff',
(forall i : nat,
    i < Datatypes.length l ->
    forall (id : nat) (eff : SideEffectList) (id' : nat) (res : Value + Exception)
      (eff' : SideEffectList),
    | env, id, nth i l ErrorExp, eff | -e> | id', res, eff' | ->
    exists clock : nat, eval_fbos_expr env id (nth i l ErrorExp) eff clock = Result id' res eff')
->
(forall j : nat,
     j < Datatypes.length vals ->
     | env, nth_def ids id 0 j, nth j l ErrorExp, nth_def eff0 eff [] j | -e>
     | nth_def ids id 0 (S j), inl (nth j vals ErrorValue), nth_def eff0 eff [] (S j) |)
->
| env, last ids id, nth (Datatypes.length vals) l ErrorExp, 
     last eff0 eff | -e> | id', inr ex, eff' | ->
Datatypes.length vals < Datatypes.length l ->
Datatypes.length ids = length vals ->
Datatypes.length eff0 = length vals ->
exists clock, (fix eval_list
     (env0 : Environment) (id0 : nat) (exps : list Expression) (eff1 : SideEffectList)
     {struct exps} : ResultListType :=
     match exps with
     | nil => LResult id0 (inl nil) eff1
     | x :: xs =>
         match eval_fbos_expr env0 id0 x eff1 clock with
         | Result id' (inl v) eff' =>
             match eval_list env0 id' xs eff' with
             | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
             | LResult id'' (inr _) _ => eval_list env0 id' xs eff'
             | _ => eval_list env0 id' xs eff'
             end
         | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
         | Timeout => LTimeout
         | Failure => LFailure
         end
     end) env id l eff = LResult id' (inr ex) eff'.
Proof.
  induction l.
  * intros. inversion H2.
  * intros. destruct vals.
    - subst. apply length_zero_iff_nil in H3. apply length_zero_iff_nil in H4. subst.
      simpl in H1. 
      assert (0 < Datatypes.length (a :: l)). { simpl. lia. }
      pose (H 0 H3 _ _ _ _ _ H1). inversion e. exists x. simpl in H4. rewrite H4. auto.
    - pose (EE1 := element_exist _ _ (eq_sym H3)).
      pose (EE2 := element_exist _ _ (eq_sym H4)).
      inversion EE1 as [id'']. inversion EE2 as [eff''].
      inversion H5. inversion H6. subst.
      clear EE1. clear EE2. clear H5. clear H6.
      assert (0 < Datatypes.length (v :: vals)). { simpl. lia. }
      assert (0 < Datatypes.length (a :: l)). { simpl. lia. }
      pose (P1 := H0 0 H5).
      pose (P2 := H 0 H6 _ _ _ _ _ P1). inversion P2. simpl in H7.
      inversion H3. inversion H4. simpl in H2. apply Lt.lt_S_n in H2.
      rewrite <- last_element_equal in H1.
      rewrite <- last_element_equal in H1.
      pose (IH := IHl env x eff'' id'' x0 vals ex id' eff' (restrict env l a H)
               (restrict_helper _ _ _ _ _ _ _ _ _ _ _ (length vals) H0) H1 H2 H9 H10).
      inversion IH.
      clear IH. clear IHl.
      exists (x1 + x2).
      apply bigger_clock with (clock' := x1 + x2) in H7. 2: lia.
      rewrite H7.
      apply bigger_clock_list with (clock' := x1 + x2) in H8. 2: lia.
      rewrite H8. auto.
Qed. *)

Theorem fbos_sound :
  forall env id exp eff id' res eff',
  | env, id, exp, eff | -e> |id', res, eff'|
->
  (exists clock, eval_fbos_expr env id exp eff clock = Result id' res eff').
Proof.
  intro. intro. intros. induction H. (* induction exp using Expression_ind_2; *) intros.
  (* 1-5: exists 1; simpl; inversion H; auto; rewrite H3; auto. *)
  1-5 :admit.
  * (* pose (list_sound _ _ _ _ _ _ _ H3).
  
  inversion H; subst.
    - pose (IHexp2 _ _ _ _ _ H4).
      pose (IHexp1 _ _ _ _ _ H9).
      inversion e. inversion e0.
      exists (S (x + x0)). simpl.
      apply bigger_clock with (clock' := x + x0) in H0.
      apply bigger_clock with (clock' := x + x0) in H1.
      rewrite H0, H1. auto. lia. lia.
    - pose (IHexp2 _ _ _ _ _ H8). inversion e.
      exists (S x).
      simpl. rewrite H0. auto.
    - pose (IHexp2 _ _ _ _ _ H4). inversion e.
      pose (IHexp1 _ _ _ _ _ H9). inversion e0.
      exists (S (x + x0)). simpl.
      apply bigger_clock with (clock' := x + x0) in H0.
      apply bigger_clock with (clock' := x + x0) in H1.
      rewrite H0, H1. auto. lia. lia.
  * inversion H0; subst.
    - pose (list_sound _ _ _ _ _ _ _ H H5 H2 H4 H3). inversion e.
      exists (S x). simpl. rewrite H1. auto.
    - pose (list_exception_sound _ _ _ _ _ _ _ _ _ _ H H6 H9 H2 H5 H4).
      inversion e. exists (S x). simpl. rewrite H1. auto. *)

Admitted.

(* Lemma list_length_equal :
forall env l id eff id' vl eff' clock,
(fix eval_list
          (env : Environment) (id : nat) (exps : list Expression) 
          (eff : SideEffectList) {struct exps} : ResultListType :=
          match exps with
          | [] => LResult id (inl []) eff
          | x0 :: xs =>
              match eval_fbos_expr env id x0 eff clock with
              | Result id' (inl v) eff' =>
                  match eval_list env id' xs eff' with
                  | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                  | LResult id'' (inr _) _ => eval_list env id' xs eff'
                  | _ => eval_list env id' xs eff'
                  end
              | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
              | Timeout => LTimeout
              | Failure => LFailure
              end
          end) env id l eff = LResult id' (inl vl) eff'
-> length l = length vl.
Proof.
  induction l; intros.
  * simpl. intros. inversion H. reflexivity.
  * intros. destruct (eval_fbos_expr env id a eff clock).
    - destruct res; simpl in *.
      + case_eq ((fix eval_list
         (env : Environment) (id : nat) (exps : list Expression) 
         (eff : SideEffectList) {struct exps} : ResultListType :=
         match exps with
         | [] => LResult id (inl []) eff
         | x0 :: xs =>
             match eval_fbos_expr env id x0 eff clock with
             | Result id' (inl v) eff' =>
                 match eval_list env id' xs eff' with
                 | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                 | LResult id'' (inr _) _ => eval_list env id' xs eff'
                 | _ => eval_list env id' xs eff'
                 end
             | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
             | Timeout => LTimeout
             | Failure => LFailure
             end
         end) env id0 l eff0); intros.
         ** destruct res.
           -- rewrite H0 in H. inversion H. simpl. apply eq_S.
              eapply IHl. apply H0.
           -- rewrite H0 in H. discriminate.
         ** rewrite H0 in H. discriminate.
         ** rewrite H0 in H. discriminate.
      + discriminate.
    - discriminate.
    - discriminate.
Qed. *)

Lemma list_correct :
forall l env id eff id' vl eff' clock,
(fix eval_list
          (env : Environment) (id : nat) (exps : list Expression) 
          (eff : SideEffectList) {struct exps} : ResultListType :=
          match exps with
          | [] => LResult id (inl []) eff
          | x0 :: xs =>
              match eval_fbos_expr env id x0 eff clock with
              | Result id' (inl v) eff' =>
                  match eval_list env id' xs eff' with
                  | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                  | LResult id'' (inr _) _ => eval_list env id' xs eff'
                  | _ => eval_list env id' xs eff'
                  end
              | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
              | Timeout => LTimeout
              | Failure => LFailure
              end
          end) env id l eff = LResult id' (inl vl) eff'
->
(
exists idl effl, 
  length l = length vl /\
  length l = length idl /\
  length l = length effl /\
  eff' = last effl eff /\
  id' = last idl id /\
  (forall i, i < length l ->
    eval_fbos_expr env (nth_def idl id 0 i) (nth i l ErrorExp) (nth_def effl eff [] i) clock =
      Result (nth_def idl id 0 (S i)) (inl (nth i vl ErrorValue)) (nth_def effl eff [] (S i))
  )
)
.
Proof.
  induction l; intros.
  * inversion H. subst. exists []. exists [].
    repeat (split; auto).
    intros. inversion H0.
  * case_eq (eval_fbos_expr env id a eff clock); intros. destruct res.
    - rewrite H0 in H. case_eq ((fix eval_list
         (env : Environment) (id : nat) (exps : list Expression) 
         (eff : SideEffectList) {struct exps} : ResultListType :=
         match exps with
         | [] => LResult id (inl []) eff
         | x0 :: xs =>
             match eval_fbos_expr env id x0 eff clock with
             | Result id' (inl v) eff' =>
                 match eval_list env id' xs eff' with
                 | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                 | LResult id'' (inr _) _ => eval_list env id' xs eff'
                 | _ => eval_list env id' xs eff'
                 end
             | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
             | Timeout => LTimeout
             | Failure => LFailure
             end
         end) env id0 l eff0); intros. destruct res.
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
forall l env id eff id' ex eff' clock,
(fix eval_list
          (env : Environment) (id : nat) (exps : list Expression) 
          (eff : SideEffectList) {struct exps} : ResultListType :=
          match exps with
          | [] => LResult id (inl []) eff
          | x0 :: xs =>
              match eval_fbos_expr env id x0 eff clock with
              | Result id' (inl v) eff' =>
                  match eval_list env id' xs eff' with
                  | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                  | LResult id'' (inr _) _ => eval_list env id' xs eff'
                  | _ => eval_list env id' xs eff'
                  end
              | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
              | Timeout => LTimeout
              | Failure => LFailure
              end
          end) env id l eff = LResult id' (inr ex) eff'
->
(
exists vals idl effl, 
  length vals < length l /\
  length vals = length idl /\
  length vals = length effl /\
  (forall i, i < length vals ->
    eval_fbos_expr env (nth_def idl id 0 i) (nth i l ErrorExp) (nth_def effl eff [] i) clock =
      Result (nth_def idl id 0 (S i)) (inl (nth i vals ErrorValue)) (nth_def effl eff [] (S i))
  ) /\
  eval_fbos_expr env (last idl id) (nth (length vals) l ErrorExp) (last effl eff) clock = Result id' (inr ex) eff'
)
.
Proof.
  induction l; intros.
  * inversion H.
  * case_eq (eval_fbos_expr env id a eff clock); intros. destruct res.
    - rewrite H0 in H.
      case_eq ((fix eval_list
         (env : Environment) (id : nat) (exps : list Expression) (eff : SideEffectList)
         {struct exps} : ResultListType :=
         match exps with
         | [] => LResult id (inl []) eff
         | x0 :: xs =>
             match eval_fbos_expr env id x0 eff clock with
             | Result id' (inl v) eff' =>
                 match eval_list env id' xs eff' with
                 | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                 | LResult id'' (inr _) _ => eval_list env id' xs eff'
                 | _ => eval_list env id' xs eff'
                 end
             | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
             | Timeout => LTimeout
             | Failure => LFailure
             end
         end) env id0 l eff0); intros. destruct res.
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
  forall exp env id eff id' res eff',
  (exists clock, eval_fbos_expr env id exp eff clock = Result id' res eff')
->
  | env, id, exp, eff | -e> |id', res, eff'|.
Proof.
  intro. induction exp using Expression_ind_2; intros.
  * inversion H. destruct x; inversion H0.
    apply eval_nil.
  * inversion H. destruct x; inversion H0.
    apply eval_lit.
  * inversion H. destruct x; inversion H0.
    apply eval_var. auto.
  * inversion H. destruct x; inversion H0.
    apply eval_funid. auto.
  * inversion H. destruct x; inversion H0.
    apply eval_fun.
  * inversion H0. destruct x; inversion H1.
    case_eq ((fix eval_list
          (env : Environment) (id : nat) (exps : list Expression) 
          (eff : SideEffectList) {struct exps} : ResultListType :=
          match exps with
          | [] => LResult id (inl []) eff
          | x0 :: xs =>
              match eval_fbos_expr env id x0 eff x with
              | Result id' (inl v) eff' =>
                  match eval_list env id' xs eff' with
                  | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                  | LResult id'' (inr _) _ => eval_list env id' xs eff'
                  | _ => eval_list env id' xs eff'
                  end
              | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
              | Timeout => LTimeout
              | Failure => LFailure
              end
          end) env id l eff); intros; subst.
    - destruct res0.
      + rewrite H2 in H3. remember (eval f6 l0 eff0) as result.
        destruct (result). inversion H3. subst. remember H2 as e1. clear Heqe1. apply list_correct in H2.
        inversion H2. inversion H4. destruct H5. destruct H6. destruct H7.
        eapply eval_call.
        ** exact H5.
        ** exact H7.
        ** exact H6.
        ** intros. apply H. assumption. eexists. apply H8. assumption.
        ** symmetry. inversion H8. rewrite <- H9. apply Heqresult.
        ** apply H8.
     + rewrite H2 in H3. inversion H3. subst.
       apply list_exception_correct in H2.
       destruct H2, H2, H2, H2, H4, H5.
       apply eval_call_ex with (i := length x0) (vals := x0) (eff := x2) (ids := x1); auto.
       ** intros. assert (j < length l). { lia. } pose (H j H8).
          apply e0. eexists. apply H6. assumption.
       ** apply H; auto. eexists. apply H6.
    - rewrite H2 in H3. congruence.
    - rewrite H2 in H3. congruence.
  * inversion H0. destruct x.
    - simpl in H1. congruence.
    - simpl in H1. case_eq (eval_fbos_expr env id exp eff x); intros. destruct res0.
      + rewrite H2 in H1. case_eq ((fix eval_list
          (env : Environment) (id : nat) (exps : list Expression) 
          (eff : SideEffectList) {struct exps} : ResultListType :=
          match exps with
          | [] => LResult id (inl []) eff
          | x0 :: xs =>
              match eval_fbos_expr env id x0 eff x with
              | Result id' (inl v) eff' =>
                  match eval_list env id' xs eff' with
                  | LResult id'' (inl xs') eff'' => LResult id'' (inl (v :: xs')) eff''
                  | LResult id'' (inr _) _ => eval_list env id' xs eff'
                  | _ => eval_list env id' xs eff'
                  end
              | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
              | Timeout => LTimeout
              | Failure => LFailure
              end
          end) env id0 l eff0); intros. destruct res0.
          ** rewrite H3 in H1. apply list_correct in H3.
             destruct v.
             -- inversion H1. destruct H3, H3.
                eapply eval_app_badfun_ex with (vals := l0) (ids := x0) (eff := x1);
                try (apply H3).
                ++ apply IHexp. eexists. exact H2.
                ++ intros. destruct H3, H8, H9, H10, H11. subst.
                   apply H. auto. exists x. subst. apply H12. auto.
                ++ intros. congruence.
                ++ subst. apply H3.
                ++ subst. apply H3.
            -- inversion H1. destruct H3, H3.
                eapply eval_app_badfun_ex with (vals := l0) (ids := x0) (eff := x1);
                try (apply H3).
                ++ apply IHexp. eexists. exact H2.
                ++ intros. destruct H3, H8, H9, H10, H11. subst.
                   apply H. auto. exists x. subst. apply H12. auto.
                ++ intros. congruence.
                ++ subst. apply H3.
                ++ subst. apply H3.
             -- case_eq (Datatypes.length l0 =? Datatypes.length vl)%nat; intros.
                ++ destruct H3, H3. destruct H3, H5, H6, H7, H8.
                  eapply eval_app with (vals := l0) (ids := x0) (eff := x1); auto.
                  *** apply IHexp. eexists. exact H2.
                  *** apply Nat.eqb_eq in H4. auto.
                  *** intros. apply H. auto. exists x. subst. apply H9. auto.
                  *** rewrite H4 in H1. admit. (* TODO: check induction hypothesis *)
                ++ rewrite H4 in H1. inversion H1. subst.
                   apply Nat.eqb_neq in H4.
                   destruct H3, H3. destruct H3, H5, H6, H7, H8.
                   eapply eval_app_badarity_ex with (vals := l0) (ids := x0) (eff := x1); auto.
                   *** apply IHexp. eexists. exact H2.
                   *** intros. apply H. auto. exists x. subst. apply H9. auto.
                   *** exact H7.
                   *** exact H8.
        ** rewrite H3 in H1. inversion H1. subst.
           apply list_exception_correct in H3. destruct H3, H3, H3, H3, H4, H5, H6.
           eapply eval_app_param_ex with (i := length x0) (vals := x0) (ids := x1) (eff := x2); auto.
           -- apply IHexp. eexists. exact H2.
           -- intros. apply H. lia. exists x. subst. apply H6. auto.
           -- apply H. auto. eexists. exact H7.
        ** rewrite H3 in H1. congruence.
        ** rewrite H3 in H1. congruence.
      + rewrite H2 in H1. destruct H0. inversion H1. subst.
        eapply eval_app_closure_ex. apply IHexp. eexists. exact H2.
      + rewrite H2 in H1. congruence.
      + rewrite H2 in H1. congruence.
  * destruct H. destruct x.
    - inversion H.
    - simpl in H. case_eq (eval_fbos_expr env id exp1 eff x); intros. destruct res0.
      + rewrite H0 in H.
        eapply eval_let.
        ** apply IHexp1. eexists. exact H0.
        ** apply IHexp2. eexists. exact H.
      + rewrite H0 in H. inversion H. subst.
        eapply eval_let_ex.
        apply IHexp1. eexists. exact H0.
      + rewrite H0 in H. congruence.
      + rewrite H0 in H. congruence.
  * destruct H. destruct x.
    - inversion H.
    - simpl in H. apply eval_letrec. apply IHexp2. eexists. exact H.
  * destruct H. destruct x.
    - inversion H.
    - simpl in H. case_eq (eval_fbos_expr env id exp1 eff x); intros. destruct res0.
      + rewrite H0 in H.
        eapply eval_try.
        ** apply IHexp1. eexists. exact H0.
        ** apply IHexp2. eexists. exact H.
      + rewrite H0 in H. inversion H. subst.
        eapply eval_catch.
        ** apply IHexp1. eexists. exact H0.
        ** apply IHexp3. eexists. simpl. exact H.
      + rewrite H0 in H. congruence.
      + rewrite H0 in H. congruence.
Admitted.


(** determinism is trivial *)
Theorem fbos_deterministic :
  forall env id exp eff clock r r',
  eval_fbos_expr env id exp eff clock = r ->
  eval_fbos_expr env id exp eff clock = r' ->
  r = r'.
Proof.
  intros. rewrite H in H0. auto.
Qed.


Example eq1 env id e eff clock :
  eval_fbos_expr env (S id) e eff clock = eval_fbos_expr env id (ELet "X"%string (EFun [] e) (EApp (EVar "X"%string) [])) eff (S (S clock)).
Proof.
  destruct clock.
  * simpl. reflexivity.
  * simpl eval_fbos_expr at 2. rewrite get_value_here. rewrite nil_length. repeat (fold eval_fbos_expr). reflexivity.
Qed.

Import List.

Arguments eval : simpl never.

Example eq2 env id eff clock A B e1 e2 v1 v2 eff1 eff2 id1 id2 t:
  eval_fbos_expr env id e1 eff clock = Result (id + id1) (inl v1) (eff ++ eff1) ->
  eval_fbos_expr env id e2 eff clock = Result (id + id2) (inl v2) (eff ++ eff2) ->
  eval_fbos_expr (insert_value env (inl B) v2) (id + id2) e1 (eff ++ eff2) clock = Result (id + id2 + id1) (inl v1) (eff ++ eff2 ++ eff1) ->
  eval_fbos_expr (insert_value env (inl A) v1) (id + id1) e2 (eff ++ eff1) clock = Result (id + id1 + id2) (inl v2) (eff ++ eff1 ++ eff2) ->
  A <> B ->
  eval_fbos_expr env id 
      (ELet B e2 (ELet A e1
        (ECall "+"%string [EVar A ; EVar B])))
      eff (S (S clock)) = Result (id + id2 + id1) (inl t) (eff ++ eff2 ++ eff1)
<->
  eval_fbos_expr env id 
      (ELet A e1 (ELet B e2
        (ECall "+"%string [EVar A ; EVar B])))
      eff (S (S clock)) = Result (id + id1 + id2) (inl t) (eff ++ eff1 ++ eff2).
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

Example eq1_pbs env id e eff id' res eff':
 |env, (S id), e, eff | -p> | id', res, eff' |
<->
 |env, id, ELet "X"%string (EFun [] e) (EApp (EVar "X"%string) []), eff| -p> |id', res, eff'|.
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
 |env, id, ELet "X"%string (EFun [] e) (EApp (EVar "X"%string) []), eff| -e> |id', res, eff'|.
Proof.
  split; intros.
  * eapply eval_let; auto.
    - apply eval_fun.
    - simpl. eapply eval_app with (vals := []) (var_list := []) (body := e) (ref := env)
                                    (ext := []) (eff := []) (eff2 := eff) (eff3 := eff') (ids := []); auto.
      + assert (get_value (insert_value env (inl "X") (VClos env [] id [] e)) (inl "X") 
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
  
  }
  {
  
  }
Qed.