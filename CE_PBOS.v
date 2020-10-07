Require Export CE_Aux.

Import ListNotations.

Inductive AuxExpression : Type :=
| AApp1 (b : Value + Exception) (params : list Expression)
| AApp2 (v : Value) (b : list Value + Exception)
| ALet (x : Var) (b : Value + Exception) (e : Expression)
| ACall (f : string) (b : list Value + Exception)
| ATry (b : Value + Exception) (v : Var) (e2 : Expression) (vl : list Var) (e3 : Expression).

Inductive AuxList : Type :=
| AList (rest : list Expression) (b : list Value + Exception).


Definition mk_result (res : Value + Exception) (vl : list Value) : list Value + Exception :=
match res with
| inl val => inl (vl ++ [val])
| inr ex => inr ex
end.


Reserved Notation "| env , id , e , eff | -a> | id' , e' , eff' |" (at level 70).
Reserved Notation "| env , id , e , eff | -p> | id' , e' , eff' |" (at level 70).
Reserved Notation "| env , id , e , eff | -l> | id' , e' , eff' |" (at level 70).
Inductive peval_aux : Environment -> nat -> AuxExpression -> SideEffectList -> nat -> Value + Exception -> SideEffectList -> Prop :=

| peval_app1_exc env id ex eff params:
  |env, id, AApp1 (inr ex) params, eff | -a> |id, inr ex, eff|

| peval_app1_fin env id id' id'' v eff eff' eff'' params res res':
  |env, id, AList params (inl []), eff| -l> |id', res, eff'| ->
  |env, id', AApp2 v res, eff | -a> |id'', res', eff'' |
->
  |env, id, AApp1 (inl v) params, eff | -a> |id'', res', eff''|

| peval_app2_fin env id id' vals eff eff' res ref ext nid var_list body:
  length var_list = length vals ->
  |append_vars_to_env var_list vals (get_env ref ext), id, body, eff| -p> |id', res, eff'|
->
  |env, id, AApp2 (VClos ref ext nid var_list body) (inl vals), eff| -a> |id', res, eff'|

| peval_app2_exc1 env id eff vals v :
  (forall ref ext var_list body n, v <> VClos ref ext n var_list body)
->
  |env, id, AApp2 v (inl vals), eff| -a> |id, inr (badfun v), eff|

| peval_app2_exc2 env id eff var_list vals ref ext body nid :
  length var_list <> length vals
->
  | env, id, AApp2 (VClos ref ext nid var_list body) (inl vals), eff | -a> |id, inr (badarity (VClos ref ext nid var_list body)), eff|

| peval_app2_exc env id eff v ex :
  |env, id, AApp2 v (inr ex), eff| -a> |id, inr ex, eff|

| peval_let_exc env id v ex e2 eff:
  | env, id, ALet v (inr ex) e2, eff | -a> | id, inr ex, eff |

| peval_let_fin env var v e2 eff id id' eff' res:
  | insert_value env (inl var) v, id, e2, eff| -p> | id', res, eff' |
->
  | env, id, ALet var (inl v) e2, eff | -a> | id', res, eff' |

| peval_call_fin env id f vals eff eff' res:
  eval f vals eff = (res, eff')
->
  | env, id, ACall f (inl vals), eff | -a> | id, res, eff' |

| peval_call_exc env id f eff ex:
  | env, id, ACall f (inr ex), eff | -a> | id, inr ex, eff |

| peval_try1_fin env id id' eff eff' v v1 e2 e3 varl res:
  |insert_value env (inl v1) v, id, e2, eff | -p> | id', res, eff'|
->
  | env, id, ATry (inl v) v1 e2 varl e3, eff | -a> | id', res, eff'|

| peval_try1_exc env id id' eff eff' ex v1 e2 e3 varl res:
  |append_try_vars_to_env varl [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env, id, e3, eff|
 -p>
  |id', res, eff'|
->
  | env, id, ATry (inr ex) v1 e2 varl e3, eff | -a> | id', res, eff'|

where "| env , id , e , eff | -a> | id' , e' , eff' |" := (peval_aux env id e eff id' e' eff')
with peval_expr : Environment -> nat -> Expression -> SideEffectList -> nat -> Value + Exception -> SideEffectList -> Prop :=

(* literal evaluation rule *)
| peval_lit (env : Environment) (l : Literal) (eff : SideEffectList) (id : nat):
  |env, id, ELit l, eff| -p> |id, inl (VLit l), eff|

(* variable evaluation rule *)
| peval_var (env:Environment) (s: Var) (eff : SideEffectList) (id : nat) (res : Value + Exception) :
  res = get_value env (inl s)
->
  |env, id, EVar s, eff| -p> |id, res, eff|

(* Function Identifier evaluation rule *)
| peval_funid (env:Environment) (fid : FunctionIdentifier) (eff : SideEffectList) 
    (res : Value + Exception) (id : nat):
  res = get_value env (inr fid)
->
  |env, id, EFunId fid, eff| -p> |id, res, eff|

(* Function evaluation *)
| peval_fun (env : Environment) (vl : list Var) (e : Expression) (eff : SideEffectList) (id : nat):
  |env, id, EFun vl e, eff| -p> |S id, inl (VClos env [] id vl e), eff|

| peval_let (env: Environment) (v : Var) (res : Value + Exception) (e1 e2 : Expression) (b : Value + Exception) (eff1 eff' eff'' : SideEffectList) (id id' id'' : nat) :
  |env, id, e1, eff1| -p> |id', b, eff'| ->
  |env, id', ALet v b e2 , eff'| -a> |id'', res, eff''|
->
  |env, id, ELet v e1 e2, eff1| -p> |id'', res, eff''|

| peval_app env id id' id'' eff eff' eff'' exp params b res:
  |env, id, exp, eff| -p> |id', b, eff'|
  ->
  |env, id', AApp1 b params, eff'| -a> |id'', res, eff''|
->
  | env, id, EApp exp params, eff | -p> |id'', res, eff''|

(* call *)
| peval_call env id id' id'' eff eff' eff'' res res' f params:
  | env, id, AList params (inl []), eff | -l> | id', res, eff' | ->
  | env, id', ACall f res, eff' | -a> | id'', res', eff'' |
->
  | env, id, ECall f params, eff | -p> | id'', res', eff'' |

(* try *)
| peval_try env id id' id'' eff eff' eff'' e1 v1 e2 e3 vlist res res':
  | env, id, e1, eff | -p> |id', res, eff'| ->
  | env, id', ATry res v1 e2 vlist e3, eff' | -a> |id'', res', eff''|
->
  | env, id, ETry e1 v1 e2 vlist e3, eff | -p> | id'', res' , eff'' |

(* letrec *)
| peval_letrec (env: Environment) (e b : Expression)  (l : list Var) (res : Value + Exception) (eff1 eff2 : SideEffectList) (f : FunctionIdentifier) (id id' : nat) :
  (
     |append_funs_to_env [(f, (l, b))] env id, S id, e, eff1| -p> | id', res, eff2|
  )
->
  |env, id, ELetRec f l b e, eff1| -p> | id', res, eff2|

where "| env , id , e , eff | -p> | id' , e' , eff' |" := (peval_expr env id e eff id' e' eff')
with peval_list : Environment -> nat -> AuxList -> SideEffectList -> nat -> list Value + Exception -> SideEffectList -> Prop :=

(* | peval_app2 env id id' id'' eff eff' eff'' v r rest vals res1 res2:
  |env, id, r, eff| -p> |id', res1, eff'| ->
  |env, id', AApp2 v rest (mk_result res1 vals), eff'| -a> |id'', res2, eff''|
->
  |env, id, AApp2 v (r::rest) (inl vals), eff| -a> |id'', res2, eff''| *)

| peval_empty env id eff vals :
  | env, id, AList [] (inl vals), eff | -l> | id, inl vals, eff|

| peval_list_cons env id id' id'' eff eff' eff'' r rest vals res res':
  | env, id, r, eff | -p> |id', res, eff'| ->
  |env, id', AList rest (mk_result res vals), eff' | -l> | id'', res', eff''|
->
  | env, id, AList (r::rest) (inl vals), eff | -l> | id, res', eff''|

| peval_list_exc env id eff rest ex:
  | env, id, AList rest (inr ex), eff | -l> | id, inr ex, eff|

where "| env , id , e , eff | -l> | id' , e' , eff' |" := (peval_list env id e eff id' e' eff')
.

Scheme peval_expr_ind2 := Induction for peval_expr Sort Prop
with   peval_list_ind2 := Induction for peval_list Sort Prop
with   peval_aux_ind2  := Induction for peval_aux  Sort Prop
.

Check peval_expr_ind2.

Combined Scheme peval_ind from peval_expr_ind2, peval_aux_ind2, peval_list_ind2.

Check peval_ind.

Ltac solve_auxpbos :=
match goal with

(* INTERMEDIATE TERMS *)
| |- |_, _, AApp1 (inr _) _, _ | -a> |_, _, _| =>
      idtac 1; eapply peval_app1_exc

| |- |_, _, AApp1 (inl _) _, _ | -a> |_, _, _| =>
      idtac 2; eapply peval_app1_fin; decider

(* Test whether this goes first *)
| |- |_, _, AApp2 (VClos _ _ _ _ _) (inl _), _| -a> |_, _, _| =>
      (idtac 3; eapply peval_app2_fin;
       match goal with
       | |- length _ = length _ => reflexivity
       | _ => solve_pbos
       end
      )
      +
      (idtac 4; eapply peval_app2_exc2; simpl; lia)

| |- |_, _, AApp2 _ (inl _), _| -a> |_, _, _| =>
      idtac 5; eapply peval_app2_exc1; unfold not; intros; congruence

| |- |_, _, AApp2 _ (inr _), _| -a> |_, _, _| =>
      idtac 6; eapply peval_app2_exc

| |- | _, _, ALet _ (inr _) _, _ | -a> | _, _, _ | =>
      eapply peval_let_exc

| |- | _, _, ALet _ (inl _) _, _ | -a> | _, _, _ | =>
      eapply peval_let_fin; solve_pbos

| |- | _, _, ACall _ (inl _), _ | -a> | _, _, _ | =>
      eapply peval_call_fin; reflexivity

| |- | _, _, ACall _ (inr _), _ | -a> | _, _, _ | =>
      eapply peval_call_exc

| |- | _, _, ATry (inl _) _ _ _ _, _ | -a> | _, _, _| =>
      eapply peval_try1_fin; solve_pbos

| |- | _, _, ATry (inr _) _ _ _ _, _ | -a> | _, _, _| =>
      eapply peval_try1_exc; solve_pbos
end
with solve_pbos :=
match goal with
(* EXPRESSIONS *)
| |- |_, _, ELit _, _| -p> |_, _, _| => eapply peval_lit
| |- |_, _, EVar _, _| -p> |_, _, _| => eapply peval_var; reflexivity
| |- |_, _, EFun _ _, _| -p> |_, _, _| => eapply peval_fun
| |- |_, _, EFunId _, _| -p> |_, _, _| => eapply peval_funid; reflexivity
| |- |_, _, ELet _ _ _, _| -p> |_, _, _| =>
      idtac 1; eapply peval_let; decider

| |- | _, _, EApp _ _, _ | -p> |_, _, _| =>
      eapply peval_app; decider

| |- | _, _, ECall _ _, _ | -p> | _, _, _ | =>
      eapply peval_call; decider

| |- | _, _, ETry _ _ _ _ _, _ | -p> | _, _ , _ | =>
      eapply peval_try; decider

| |- |_, _, ELetRec _ _ _ _, _| -p> | _, _, _| =>
      eapply peval_letrec; simpl; solve_pbos
end
(* LISTS *)
with solve_plist :=
match goal with
| |- | _, _, AList [] (inl _), _ | -l> | _, _, _| =>
      idtac 21; eapply peval_empty
| |- | _, _, AList _ (inr _), _ | -l> | _, _, _| =>
      idtac 22; eapply peval_list_exc
| |- | _, _, AList (_::_) (inl _), _ | -l> | _, _, _| =>
      idtac 23; eapply peval_list_cons; decider

(* This is needed to simplify mk_result *)
| |- | _, _, AList _ _, _ | -l> | _, _, _| =>
      idtac 24; simpl; solve_pbos
end
with decider :=
match goal with
| |- | _, _, _, _ | -p> | _, _, _ | => simpl; solve_pbos
| |- | _, _, _, _ | -l> | _, _, _ | => simpl; solve_plist
| |- | _, _, _, _ | -a> | _, _, _ | => simpl; solve_auxpbos
end
.

Open Scope string_scope.

Theorem peval_determinism :
(
  forall env id exp eff id' res eff', | env, id, exp, eff | -p> | id', res, eff' |
->
  (forall id'' res' eff'', |env, id, exp, eff| -p> |id'', res', eff''| -> id' = id'' /\ res = res' /\ eff' = eff'')
)
(* with peval_determinism2: *) /\
(forall env id exp eff id' res eff',
  | env, id, exp, eff | -a> | id', res, eff' |
->
  (forall id'' res' eff'', |env, id, exp, eff| -a> |id'', res', eff''| -> id' = id'' /\ res = res' /\ eff' = eff'')
)
(* with peval_determinism3: *) /\
( forall env id exp eff id' res eff',
  | env, id, exp, eff | -l> | id', res, eff' |
->
  (forall id'' res' eff'', |env, id, exp, eff| -l> |id'', res', eff''| -> id' = id'' /\ res = res' /\ eff' = eff'')
)
.
Proof.
  apply (* intro. induction H using  *)peval_ind; intros.
  * inversion H. subst. auto.
  * inversion H. subst. auto.
  * inversion H. subst. auto.
  * inversion H. subst. auto.
  * inversion H1. subst. apply H in p. destruct p, H3. subst. apply H0 in p0. destruct p0, H6. subst. apply H0. apply H in H11. destruct H11, H9. subst. assumption.
  * inversion H1. subst. apply H in H6. destruct H6, H3. subst. apply H0 in H11. destruct H11, H3. subst. auto.
  * inversion H1. subst. apply H in H6. destruct H6, H3. subst. apply H0 in H11. destruct H11, H3. subst. auto.
  * inversion H1. subst. apply H in H13. destruct H13, H3. subst. apply H0 in H14. destruct H14, H3. subst. auto.
  * inversion H0. subst. apply H in H11. destruct H11, H2. subst. auto.
  * inversion H. subst. auto.
  * inversion H1. subst. apply H in H11. destruct H11, H3. subst. apply H0 in H12. destruct H12, H3. subst. auto.
  * inversion H. auto.
  * inversion H. auto.
  * inversion H1. subst. apply H in H6. destruct H6, H3. subst. apply H0. assumption.
  * inversion H0; subst.
    - apply H in H14. assumption.
    - congruence.
    - congruence.
  * inversion H; subst.
    - congruence.
    - auto.
    - congruence.
  * inversion H; subst.
    - congruence.
    - congruence.
    - auto.
  * inversion H. subst. auto.
  * inversion H; subst. auto.
  * inversion H0. subst. apply H in H10. assumption.
  * inversion H. subst. rewrite H8 in e. inversion e. auto.
  * inversion H. subst. auto.
  * inversion H0. subst. apply H in H12. assumption.
  * inversion H0. subst. apply H in H12. assumption.
Qed.

Theorem peval_expr_determinism :
  forall env id exp eff id' res eff', | env, id, exp, eff | -p> | id', res, eff' |
->
  (forall id'' res' eff'', |env, id, exp, eff| -p> |id'', res', eff''| -> id' = id'' /\ res = res' /\ eff' = eff'').
Proof.
  apply peval_determinism.
Qed.

Theorem peval_aux_determinism :
  forall env id exp eff id' res eff', | env, id, exp, eff | -a> | id', res, eff' |
->
  (forall id'' res' eff'', |env, id, exp, eff| -a> |id'', res', eff''| -> id' = id'' /\ res = res' /\ eff' = eff'').
Proof.
  apply peval_determinism.
Qed.

Theorem peval_list_determinism :
  forall env id exp eff id' res eff', | env, id, exp, eff | -l> | id', res, eff' |
->
  (forall id'' res' eff'', |env, id, exp, eff| -l> |id'', res', eff''| -> id' = id'' /\ res = res' /\ eff' = eff'').
Proof.
  apply peval_determinism.
Qed.
