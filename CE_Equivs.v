Require Export CE_FBOS.
Require Export CE_NOS.

Require Import Coq.Logic.FunctionalExtensionality.

Import ListNotations.

Axiom Expression_ind_2 :
forall P : Expression -> Prop,
       P ENil ->
       (forall l : Literal, P (ELit l)) ->
       (forall v : Var, P (EVar v)) ->
       (forall f2 : FunctionIdentifier, P (EFunId f2)) ->
       (forall (vl : list Var) (e : Expression), P e -> P (EFun vl e)) ->
       (forall hd : Expression, P hd -> forall tl : Expression, P tl -> P (ECons hd tl)) ->
       (forall l : list Expression, 
         (forall i : nat, i < length l -> P (nth i l ENil)) ->
       P (ETuple l)) ->
       (forall (f6 : string) (l : list Expression), 
         (forall i : nat, i < length l -> P (nth i l ENil)) ->
       P (ECall f6 l)) ->
       (forall exp : Expression, P exp -> 
        forall l : list Expression,
         (forall i : nat, i < length l -> P (nth i l ENil)) ->
        P (EApp exp l)) ->
       (forall e : Expression,
        P e -> forall l : list (Pattern * Expression * Expression), 
          (forall i : nat, i < length l -> P (snd (fst (nth i l (PNil, ENil, ENil))))) ->
          (forall i : nat, i < length l -> P (snd (nth i l (PNil, ENil, ENil)))) ->
        P (ECase e l)) ->
       (forall (v : Var) (e1 : Expression),
        P e1 -> forall e2 : Expression, P e2 -> P (ELet v e1 e2)) ->
       (forall (f10 : FunctionIdentifier) (l : list Var) (b : Expression),
        P b -> forall e : Expression, P e -> P (ELetRec f10 l b e)) ->
       (forall e1 : Expression,
        P e1 ->
        forall (v1 : Var) (e2 : Expression),
        P e2 -> forall (vl2 : list Var) (e3 : Expression), P e3 -> P (ETry e1 v1 e2 vl2 e3)) ->
       forall e : Expression, P e.

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
    - simpl in H. case_eq (eval_fbos_expr env id exp2 eff clock); intros.
      + case_eq res0; intros; subst.
        ** rewrite H0 in H. pose (IHclock _ _ _ _ _ _ _ H0).
           case_eq (eval_fbos_expr env id0 exp1 eff0 clock); intros.
           -- case_eq res0; intros; subst.
             ++ rewrite H1 in H. pose (IHclock _ _ _ _ _ _ _ H1).
                remember (S clock) as cl. simpl.
                rewrite e. rewrite e0.
                auto.
             ++ rewrite H1 in H. pose (IHclock _ _ _ _ _ _ _ H1).
                remember (S clock) as cl. simpl.
                rewrite e. rewrite e1.
                auto.
          -- rewrite H1 in H. discriminate.
          -- rewrite H1 in H. discriminate.
        ** rewrite H0 in H. pose (IHclock _ _ _ _ _ _ _ H0).
           remember (S clock) as cl. simpl. rewrite e0.
           auto.
      + rewrite H0 in H. discriminate.
      + rewrite H0 in H. discriminate.
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
    -
Admitted.

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

Theorem restrict env l a :
(forall i : nat,
    i < Datatypes.length (a :: l) ->
    forall (id : nat) (eff : SideEffectList) (id' : nat) (res : Value + Exception)
      (eff' : SideEffectList),
    | env, id, nth i (a :: l) ENil, eff | -e> | id', res, eff' | ->
    exists clock : nat,
      eval_fbos_expr env id (nth i (a :: l) ENil) eff clock = Result id' res eff')
->
forall i : nat,
    i < Datatypes.length l ->
    forall (id : nat) (eff : SideEffectList) (id' : nat) (res : Value + Exception)
      (eff' : SideEffectList),
    | env, id, nth i l ENil, eff | -e> | id', res, eff' | ->
    exists clock : nat,
      eval_fbos_expr env id (nth i l ENil) eff clock = Result id' res eff'.
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
    | env, id, nth i l ENil, eff | -e> | id', res, eff' | ->
    exists clock : nat, eval_fbos_expr env id (nth i l ENil) eff clock = Result id' res eff')
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
    | env, id, nth i l ENil, eff | -e> | id', res, eff' | ->
    exists clock : nat, eval_fbos_expr env id (nth i l ENil) eff clock = Result id' res eff')
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
Qed.

Theorem fbos_sound :
  forall env id exp eff id' res eff',
  | env, id, exp, eff | -e> |id', res, eff'|
->
  (exists clock, eval_fbos_expr env id exp eff clock = Result id' res eff').
Proof.
  intro. intro. intro. generalize dependent id. induction exp using Expression_ind_2; intros.
  1-5: exists 1; simpl; inversion H; auto; rewrite H3; auto.
  * inversion H; subst.
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
      inversion e. exists (S x). simpl. rewrite H1. auto.

Admitted.

Theorem fbos_correct :
  forall env id exp eff id' res eff',
  (exists clock, eval_fbos_expr env id exp eff clock = Result id' res eff')
->
  | env, id, exp, eff | -e> |id', res, eff'|.
Proof.
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

Example div_expr_example : Expression :=
  ELetRec ("f", 0) [] (ELet "X" (ECall "fwrite" [ELit (Atom "a")]) 
                         (EApp (EFunId ("f", 0)) []))
       (EApp (EFunId ("f", 0)) []).


Theorem clock_decrease :
  forall clock env id exp eff,
  eval_fbos_expr env id exp eff (S clock) = Timeout
->
  eval_fbos_expr env id exp eff clock = Timeout.
Proof.
Admitted.


Example div :
  forall clock env id eff, eval_fbos_expr env id div_expr_example eff clock = Timeout.
Proof.
  induction clock.
  * auto.
  * intros. simpl.
    unfold append_funs_to_env. simpl.
    pose (IHclock env id (eff ++ [(Output, [VLit (Atom "a")])])).
    destruct clock.
    - auto.
    - simpl in *.
      destruct clock.
      + auto.
      + simpl. rewrite get_value_here. rewrite nil_length.
        (* remember (EApp (EFunId ("f", 0)) []) as appl. *)
        destruct clock.
        ** auto.
        ** simpl. destruct clock.
          -- auto.
          -- simpl.
             apply clock_decrease in e.
             simpl in e. unfold append_funs_to_env in e. simpl in e.
             rewrite get_value_here in e.
             rewrite nil_length in e.
             unfold get_env. simpl.
             rewrite get_value_there, get_value_here. 2: congruence. rewrite nil_length.
             exact e.
Qed.

