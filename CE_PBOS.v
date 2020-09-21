Require Export CE_Aux.

Import ListNotations.

Inductive AuxExpression : Type :=
| AExp (e : Expression)
| AApp1 (b : Value + Exception) (params : list Expression)
| AApp2 (v : Value) (rest : list Expression) (b : list Value + Exception)
| AApp3 (v : Value) (vals : list Value).


Definition mk_result (res : Value + Exception) (vl : list Value) : list Value + Exception :=
match res with
| inl val => inl (vl ++ [val])
| inr ex => inr ex
end.


Reserved Notation "| env , id , e , eff | -a> | id' , e' , eff' |" (at level 70).
Reserved Notation "| env , id , e , eff | -e> | id' , e' , eff' |" (at level 70).
Inductive eval_aux : Environment -> nat -> AuxExpression -> SideEffectList -> nat -> Value + Exception -> SideEffectList -> Prop :=

| eval_app1_exc env id ex eff params:
  |env, id, AApp1 (inr ex) params, eff | -a> |id, inr ex, eff|

| eval_app1_fin env id id' v eff eff' params res:
  |env, id, AApp2 v params (inl []), eff| -a> |id', res, eff'|
->
  |env, id, AApp1 (inl v) params, eff | -a> |id', res, eff'|

| eval_app2_fin env id id' v vals eff eff' res:
  |env, id, AApp3 v vals, eff| -a> |id', res, eff'|
->
  |env, id, AApp2 v [] (inl vals), eff| -a> |id', res, eff'|

| eval_app2_exc env id eff v rest ex :
  |env, id, AApp2 v rest (inr ex), eff| -a> |id, inr ex, eff|

| eval_app2 env id id' id'' eff eff' eff'' v r rest vals res1 res2:
  |env, id, r, eff| -e> |id', res1, eff'| ->
  |env, id', AApp2 v rest (mk_result res1 vals), eff'| -a> |id'', res2, eff''|
->
  |env, id, AApp2 v (r::rest) (inl vals), eff| -a> |id'', res2, eff''|

| eval_app3 env id id' eff eff' var_list vals ref ext body nid res:
  length var_list = length vals ->
  |append_vars_to_env var_list vals (get_env ref ext), id, body, eff| -e> |id', res, eff'|
->
  | env, id, AApp3 (VClos ref ext nid var_list body) vals, eff | -a> |id', res, eff'|

| eval_app3_exc1 env id id' eff eff' vals v res:
  (forall ref ext var_list body n, v <> VClos ref ext n var_list body)
->
  | env, id, AApp3 v vals, eff | -a> |id', res, eff'|

| eval_app3_exc2 env id id' eff eff' var_list vals ref ext body nid :
  length var_list <> length vals
->
  | env, id, AApp3 (VClos ref ext nid var_list body) vals, eff | -a> |id', inr (badarity (VClos ref ext nid var_list body)), eff'|

where "| env , id , e , eff | -a> | id' , e' , eff' |" := (eval_aux env id e eff id' e' eff')
with eval_expr : Environment -> nat -> Expression -> SideEffectList -> nat -> Value + Exception -> SideEffectList -> Prop :=
| eval_nil (env : Environment) (eff : SideEffectList) (id : nat):
  |env, id, ENil, eff| -e> |id, inl VNil, eff|

(* literal evaluation rule *)
| eval_lit (env : Environment) (l : Literal) (eff : SideEffectList) (id : nat):
  |env, id, ELit l, eff| -e> |id, inl (VLit l), eff|

(* variable evaluation rule *)
| eval_var (env:Environment) (s: Var) (eff : SideEffectList) (id : nat) (res : Value + Exception) :
  res = get_value env (inl s)
->
  |env, id, EVar s, eff| -e> |id, res, eff|

(* Function Identifier evaluation rule *)
| eval_funid (env:Environment) (fid : FunctionIdentifier) (eff : SideEffectList) 
    (res : Value + Exception) (id : nat):
  res = get_value env (inr fid)
->
  |env, id, EFunId fid, eff| -e> |id, res, eff|

(* Function evaluation *)
| eval_fun (env : Environment) (vl : list Var) (e : Expression) (eff : SideEffectList) (id : nat):
  |env, id, EFun vl e, eff| -e> |S id, inl (VClos env [] id vl e), eff|

(* Let : TODO this rule is not "pretty" *)
| eval_let (env: Environment) (v : Var) (val : Value) (e1 e2 : Expression) (res : Value + Exception) (eff1 eff' eff'' : SideEffectList) (id id' id'' : nat) :
  |env, id, e1, eff1| -e> |id', inl val, eff'| ->
  |append_vars_to_env [v] [val] env, id', e2, eff'| -e> |id'', res, eff''|
->
  |env, id, ELet v e1 e2, eff1| -e> |id'', res, eff''|

| eval_app env id id' id'' eff eff' eff'' exp params b res:
  |env, id, exp, eff| -e> |id', b, eff'|
  ->
  |env, id', AApp1 b params, eff'| -a> |id'', res, eff''|
->
  | env, id, EApp exp params, eff | -e> |id', res, eff'|

where "| env , id , e , eff | -e> | id' , e' , eff' |" := (eval_expr env id e eff id' e' eff')
.

Open Scope string_scope.

Goal
  | [], 0, ELet "X" (EFun ["Y"; "Z"] (EVar "Y")) (EApp (EVar "X") [ELit (Atom "a"); ELit (Atom "b")]), []|
-e>
  | 1, inl (VLit (Atom "a")), []|
.
Proof.
  eapply eval_let.
  * eapply eval_fun.
  * simpl. eapply eval_app.
    - eapply eval_var. reflexivity.
    - simpl. apply eval_app1_fin.
      + eapply eval_app2.
        ** apply eval_lit.
        ** eapply eval_app2.
          -- apply eval_lit.
          -- apply eval_app2_fin.
            ++ apply eval_app3.
              *** reflexivity.
              *** apply eval_var. reflexivity.
Qed.