Require Export CE_FBOS.
Require Export CE_NOS.

Require Import Coq.Logic.FunctionalExtensionality.

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

Theorem alma :
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
    pose (alma _ _ _ _ _ _ _ _ IHclock Heqresult). rewrite e in H0.
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
    pose (alma _ _ _ _ _ _ _ _ IHclock Heqresult). rewrite e in H0.
    clear e. clear Heqresult.
    remember (S clock) as cl. simpl. rewrite H0. assumption.
Admitted.

Theorem bigger_clock :
  forall clock clock' env id exp eff id' res eff',
  clock < clock' ->
  eval_fbos_expr env id exp eff clock = Result id' res eff'
->
  eval_fbos_expr env id exp eff clock' = Result id' res eff'.
Proof.
  intros. induction H.
  * apply clock_increase. auto.
  * apply clock_increase. auto.
Qed.

Theorem nos_equiv_fbos :
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
      exists (S (x + x0)). simpl. admit.
    - admit.
    - admit.
  * inversion H0. subst.
    exists (S ?[r]).


















