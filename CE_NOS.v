Require Export CE_Aux.

Import ListNotations.

(** End of tests *)

Reserved Notation "| env , id , e , eff | -e> | id' , e' , eff' |" (at level 70).
Inductive eval_expr : Environment -> nat -> Expression -> SideEffectList -> nat -> Value + Exception -> SideEffectList -> Prop :=
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

(* tuple evaluation rule *)
| eval_tuple (env: Environment) (exps : list Expression) (vals : list Value) 
     (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) :
  length exps = length vals ->
  length exps = length eff ->
  length exps = length ids ->
  (
    forall i, i < length exps ->
      |env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i| 
     -e> 
      |nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff1 [] (S i)|
  ) ->
  eff2 = last eff eff1 ->
  id' = last ids id (* if length = 0, then last id = first id *)
->
  |env, id, ETuple exps, eff1| -e> |id' , inl (VTuple vals), eff2|

(* list evaluation rule *)
| eval_cons (env:Environment) (hd tl: Expression) (hdv tlv : Value) 
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, tl, eff1| -e> |id', inl tlv, eff2| ->
  |env, id', hd, eff2| -e> | id'', inl hdv, eff3|
->
  |env, id, ECons hd tl, eff1| -e> |id'', inl (VCons hdv tlv), eff3|

(* case evaluation rules *)
| eval_case (env: Environment) (guard exp: Expression) (e : Expression) (val : Value) (res : Value + Exception) (l : list (Pattern * Expression * Expression)) (bindings: list (Var * Value)) (i : nat) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, e, eff1| -e> |id', inl val, eff2| ->
  i < length l ->
  match_clause val l i = Some (guard, exp, bindings) ->
  (forall j : nat, j < i -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause val l j = Some (gg, ee, bb) -> 
      (|add_bindings bb env, id', gg, eff2| -e> |id', inl ffalse, eff2| ))

  ) ->
  |add_bindings bindings env, id', guard, eff2| -e> |id', inl ttrue, eff2| -> 
  |add_bindings bindings env, id', exp, eff2| -e> |id'', res, eff3|
->
  |env, id, ECase e l, eff1| -e> |id'', res, eff3|


(* call evaluation rule *)
| eval_call (env: Environment) (res : Value + Exception) (params : list Expression) 
     (vals : list Value) (fname: string) (eff1 eff2: SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' : nat) :
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, nth_def ids id 0 i, nth i params ErrorExp, nth_def eff eff1 [] i| 
     -e>
      |nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff1 [] (S i)|
  ) ->
  eval fname vals (last eff eff1) = (res, eff2) ->
  id' = last ids id
->
  |env, id, ECall fname params, eff1| -e> |id', res, eff2|

(* apply functions*)
| eval_app (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (body : Expression) (res : Value + Exception) (var_list : list Var) 
     (ref : Environment) (ext : list (nat * FunctionIdentifier * FunctionExpression)) (n : nat)
     (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat) :
  length params = length vals ->
  |env, id, exp, eff1| -e> |id', inl (VClos ref ext n var_list body), eff2| ->
  length var_list = length vals
  ->
  length params = length eff ->
  length params = length ids ->
  (
    forall i, i < length params ->
      |env, nth_def ids id' 0 i, nth i params ErrorExp, nth_def eff eff2 [] i|
     -e>
      |nth_def ids id' 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff2 [] (S i)|
  )
  ->
  |append_vars_to_env var_list vals (get_env ref ext), 
   last ids id',
   body, 
   last eff eff2|
  -e>
   |id'', res, eff3|
->
  |env, id, EApp exp params, eff1| -e> |id'', res, eff3|

(* let evaluation rule *)
| eval_let (env: Environment) (v : Var) (val : Value) (e1 e2 : Expression) (res : Value + Exception) (eff1 eff' eff'' : SideEffectList) (id id' id'' : nat) :
  |env, id, e1, eff1| -e> |id', inl val, eff'| ->
  |append_vars_to_env [v] [val] env, id', e2, eff'| -e> |id'', res, eff''|
->
  |env, id, ELet v e1 e2, eff1| -e> |id'', res, eff''|

(* Letrec evaluation rule *)
| eval_letrec (env: Environment) (e b : Expression)  (l : list Var) (res : Value + Exception) (eff1 eff2 : SideEffectList) (f : FunctionIdentifier) (id id' : nat) :
  (
     |append_funs_to_env [(f, (l, b))] env id, S id, e, eff1| -e> | id', res, eff2|
  )
->
  |env, id, ELetRec f l b e, eff1| -e> | id', res, eff2|



  (* EXCEPTIONS *)
(* list tail exception *)
| eval_cons_tl_ex (env: Environment) (hd tl : Expression) (ex : Exception) 
      (eff1 eff2 : SideEffectList) (id id' : nat) :
  |env, id, tl, eff1| -e> |id', inr ex, eff2|
->
  |env, id, ECons hd tl, eff1| -e> |id', inr ex, eff2|

(* list head exception *)
| eval_cons_hd_ex (env: Environment) (hd tl : Expression) (ex : Exception) (vtl : Value) 
     (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, tl, eff1| -e> |id', inl vtl, eff2| -> 
  |env, id', hd, eff2| -e> |id'', inr ex, eff3|
->
  |env, id, ECons hd tl, eff1| -e> |id'', inr ex, eff3|


(* tuple exception *)
| eval_tuple_ex (env: Environment) (i : nat) (exps : list Expression) (vals : list Value) 
     (ex : Exception) (eff1 eff2 : SideEffectList) (eff : list SideEffectList) 
     (id id' : nat) (ids : list nat) :
  i < length exps ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j|
   -e>
    |nth_def ids id 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff1 [] (S j)|) ->
  |env, last ids id, nth i exps ErrorExp, last eff eff1| -e> |id', inr ex, eff2|
->
  |env, id, ETuple exps, eff1| -e> |id', inr ex, eff2|


(* try 2x *)
| eval_try (env: Environment) (v1 : Var) (vl2 : list Var) (e1 e2 e3 : Expression) (res : Value + Exception) (val : Value) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, e1, eff1| -e> | id', inl val, eff2| ->
  |append_vars_to_env [v1] [val] env, id', e2, eff2 | -e> | id'', res, eff3|
->
  |env, id, ETry e1 v1 e2 vl2 e3, eff1| -e> | id'', res, eff3|


(* catch *)
| eval_catch (env: Environment) (v1 : Var) (vl2 : list Var) (e1 e2 e3 : Expression) (res : Value + Exception) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) (ex : Exception) :
  |env, id, e1, eff1| -e> |id', inr ex, eff2| ->
  |append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env, id', e3, eff2|
 -e> 
  |id'', res, eff3|
->
  |env, id, ETry e1 v1 e2 vl2 e3, eff1| -e> |id'', res, eff3|


(* case 2x *)
(** Pattern matching exception *)
| eval_case_pat_ex (env: Environment) (e : Expression) (ex : Exception) (l : list (Pattern * Expression * Expression)) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, id, e, eff1| -e> |id', inr ex, eff2|
->
  |env, id, ECase e l, eff1| -e> |id', inr ex, eff2|

(** No matching clause *)
| eval_case_clause_ex (env: Environment) (e : Expression) (l : list (Pattern * Expression * Expression)) (val : Value) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, id, e, eff1| -e> |id', inl val, eff2| ->
  (forall j : nat, j < length l -> 

    (** THESE GUARDS MUST BE SIDE-EFFECT FREE ACCORDING TO 1.0.3 LANGUAGE SPECIFICATION *)
    (forall gg ee bb, match_clause val l j = Some (gg, ee, bb) -> 
      ((|add_bindings bb env, id', gg, eff2| -e> | id', inl ffalse, eff2| ))

    )

  )
->
  |env, id, ECase e l, eff1| -e> | id', inr (if_clause), eff2|
(** ith guard exception -> guards cannot result in exception, i.e. this rule is not needed *)


(* call 1x *)
| eval_call_ex (env: Environment) (i : nat) (fname : string) (params : list Expression) 
     (vals : list Value) (ex : Exception) (eff1 eff2 : SideEffectList) 
     (eff : list SideEffectList) (id id' : nat) (ids : list nat) :
  i < length params ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_def ids id 0 j, nth j params ErrorExp, nth_def eff eff1 [] j|
   -e>
    |nth_def ids id 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff1 [] (S j)|
  ) ->
  |env, last ids id, nth i params ErrorExp, last eff eff1| -e> |id', inr ex, eff2|

->
  |env, id, ECall fname params, eff1| -e> |id', inr ex, eff2|


(* apply 4x *)
(** According to ref. implementation, here it is not needed to check the arg number *)

(** if name expression evaluates to exception *)
| eval_app_closure_ex (params : list Expression) (env : Environment) (exp : Expression)  
     (ex : Exception) (eff1 eff2 : SideEffectList) (id id' : nat):
  |env, id, exp, eff1| -e> |id', inr ex, eff2|
->
  |env, id, EApp exp params, eff1| -e> |id', inr ex, eff2|

(** name expression and some parameters evaluate to values *)
| eval_app_param_ex (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (ex : Exception) (i : nat) (v : Value) (eff1 eff2 eff3 : SideEffectList) 
     (eff : list SideEffectList) (ids : list nat) (id id' id'' : nat) :
  i < length params ->
  length vals = i ->
  length eff = i ->
  length ids = i
  ->
  |env, id, exp, eff1| -e> |id', inl v, eff2| ->
  (forall j, j < i -> 
    |env, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
   -e>
    |nth_def ids id' 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff2 [] (S j)|
  ) ->
  |env, last ids id', nth i params ErrorExp, last eff eff2| -e> |id'', inr ex, eff3|
->
  |env, id, EApp exp params, eff1| -e> |id'', inr ex, eff3|

(** Then we check if the name expression evaluates to a closure *)
| eval_app_badfun_ex (params : list Expression) (vals: list Value) (env : Environment) (v : Value) 
     (exp : Expression) (eff1 eff2 eff3 : SideEffectList) (eff : list SideEffectList) 
     (ids : list nat) (id id' id'' : nat):
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, exp, eff1| -e> |id', inl v, eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
     -e>
      |nth_def ids id' 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff2 [] (S j)|
    )
  ) ->
  (forall ref ext var_list body n, 
     v <> VClos ref ext n var_list body) ->
  eff3 = last eff eff2 ->
  id'' = last ids id'
->
  |env, id, EApp exp params, eff1| -e> |id'', inr (badfun v), eff3|

(** too few or too many arguments are given *)
| eval_app_badarity_ex (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (body : Expression) (var_list : list Var) (ref : Environment) 
     (ext : list (nat * FunctionIdentifier * FunctionExpression)) (eff1 eff2 eff3 : SideEffectList) 
     (eff : list SideEffectList) (n : nat) (ids : list nat) (id id' id'' : nat):
  length params = length vals ->
  length params = length eff ->
  length params = length ids ->
  |env, id, exp, eff1| -e> |id', inl (VClos ref ext n var_list body), eff2| ->
  (
    forall j : nat, j < length params ->
    (
      |env, nth_def ids id' 0 j, nth j params ErrorExp, nth_def eff eff2 [] j|
     -e>
      |nth_def ids id' 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff2 [] (S j)|
    )
  ) ->
  length var_list <> length vals ->
  eff3 = last eff eff2 ->
  id'' = last ids id'
->
  |env, id, EApp exp params, eff1| 
  -e> 
  |id'', inr (badarity (VClos ref ext n var_list body)), eff3|

(* let 1x *)
| eval_let_ex (env: Environment) (v1: Var) (e1 e2 : Expression) (ex : Exception) (eff1 eff2 : SideEffectList) (id id' : nat) :
  |env, id, e1, eff1| -e> |id', inr ex, eff2|
->
  |env, id, ELet v1 e1 e2, eff1| -e> | id', inr ex, eff2|


where "| env , id , e , eff | -e> | id' , e' , eff' |" := (eval_expr env id e eff id' e' eff')
.

Section Tactic.

Theorem length_succ {B : Type} (a2 : B) (n : nat) (l2 : list B):
n = length l2
->
S n = length (a2 :: l2).
Proof.
  intros. simpl. rewrite H. auto.
Qed.

Ltac simpl_app :=
  repeat (rewrite app_assoc);
  repeat (rewrite app_nil_r).

Ltac simpl_app_H Hyp0 :=
  repeat (rewrite app_assoc in Hyp0);
  repeat (rewrite app_nil_r in Hyp0).

Ltac finishing_tactic :=
unfold nth_def; simpl;
match goal with
| |- | ?env, ?id, ENil, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_nil
| |- | ?env, ?id, ELit ?lit, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_lit
| |- | ?env, ?id, EVar ?v, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_var; reflexivity
| |- | ?env, ?id, EFunId ?fid, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_funid; reflexivity
| |- | ?env, ?id, EFun ?pl ?b, ?eff | -e> | ?id', ?res, ?eff'| => apply eval_fun
end
.

Ltac empty_list :=
simpl;
match goal with
| |- 0 = length ?l => apply eq_sym, length_zero_iff_nil; reflexivity
| |- length ?l = 0 => apply length_zero_iff_nil; reflexivity
end.

Ltac unfold_list :=
simpl; 
match goal with
| |- length ?l = _ => symmetry; repeat (eapply length_succ); empty_list
| |- _ = length ?l => repeat (eapply length_succ); empty_list
| _ => idtac
end.

(** Solver tactic *)
Ltac solve :=
unfold nth_def; simpl;
match goal with
| |- | ?env, ?id, ENil, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, ENil, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, ELit ?lit, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EVar ?v, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EFunId ?fid, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EFun ?pl ?b, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, ETuple ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     (* (apply quick_tuple_eval; simpl; reflexivity)
     + *)
     (eapply eval_tuple;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     + tuple_exception_solver 0
| |- | ?env, ?id, ECons _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (* (apply quick_list_eval; simpl; reflexivity)
     + *)
     (eapply eval_cons; solve_inners)
     +
     (eapply eval_cons_tl_ex; solve_inners)
     +
     (eapply eval_cons_hd_ex; solve_inners)
| |- | ?env, ?id, ECase _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     case_solver 0
     +
     (eapply eval_case_pat_ex;
      solve_inners)
     +
     (eapply eval_case_clause_ex;
      (* unfold_list2;
      match goal with
      | |- forall i, i < length _ -> |_, _, _, _| -e> |_, _, _| =>
                                            unfold_elements;
                                            try(solve_inners)
      | _ => idtac
      end; *)
      solve_inners;
      intros;
      unfold_elements;
      match goal with
      
      | [H : match_clause _ _ _ = Some _ |- _] => inversion H
      | _ => idtac
      end;
      try(simpl;reflexivity);
      solve_inners)
| |- | ?env, ?id, ECall _ ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_call;
     unfold_list2;
     solve_inners;
     unfold_elements;
     solve_inners;
     match goal with
     | |- eval _ _ _ = _ => tryif reflexivity then idtac else fail 1
     | _ => idtac
     end;
     auto)
     +
     (call_exception_solver 0)

| |- | ?env, ?id, EApp _ _, ?eff | -e> | ?id', ?res, ?eff'| => 
     (eapply eval_app;
     unfold_list2;
     unfold_elements;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     +
     (eapply eval_app_closure_ex; solve_inners)
     +
     (app_param_exception_solver 0)
     +
     (eapply eval_app_badfun_ex;
      unfold_list2;
      unfold_elements;
      solve_inners;
      try(simpl;reflexivity);
      try(congruence)
     )
     +
     (eapply eval_app_badarity_ex;
      unfold_list2;
      unfold_elements;
      solve_inners;
      try(simpl;reflexivity);
      try(congruence)
     )
| |- | ?env, ?id, ELet _ _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_let;
     solve_inners;
     try(simpl;reflexivity);
     auto)
     +
     (eapply eval_let_ex;
      solve_inners)
| |- | ?env, ?id, ELetRec _ _ _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     eapply eval_letrec;
     solve_inners
| |- | ?env, ?id, ETry _ _ _ _ _, ?eff | -e> | ?id', ?res, ?eff'| =>
     (eapply eval_try;
      unfold_list2;
      solve_inners
      auto)
     +
     (
      eapply eval_catch;
      solve_inners
     )
end
with unfold_list2 :=
match goal with
| |- ?n = length ?l => unfold_list
| |- length ?l = ?n => unfold_list
| _ => idtac
end
with unfold_elements :=
intros; simpl length in *;
match goal with
| [H : S ?i <= 0 |-_ ] => inversion H
| [H : ?i < 0 |-_ ] => inversion H
| [H : S ?i <= ?n |-_ ] => inversion H; clear H; subst; unfold_elements
| [H : ?i < ?n |-_ ] => inversion H; clear H; subst; unfold_elements
| _ => idtac
end
with
solve_inners :=
match goal with
| |- | _, _, _, _ | -e> | _, _, _ | => tryif solve then idtac else fail 1
| |- | _, _, _, _ | -e> | _, _, _ | => tryif solve then idtac else fail 1
| _ => idtac
end
with
case_solver num :=
  tryif 
    eapply eval_case with (i := num);
    match goal with
    | |- _ < _ => tryif simpl; lia then idtac else fail 2
    | _ => idtac
    end;
    try solve_inners;
    match goal with
     | |- match_clause _ _ _ = _ => tryif reflexivity then idtac else fail 1
     | _ => idtac
    end;
    match goal with
    | |- |_, _, _, _| -e> |_, inl ttrue, _| => tryif solve then idtac else fail 1
    | _ => idtac
    end;
    unfold_elements;
    match goal with
     | [H : match_clause _ _ _ = Some _ |- _] => inversion H
     | _ => idtac
    end;
    solve_inners;
    auto
  then idtac
  else
     case_solver (S num)
with
tuple_exception_solver num :=
  match goal with
  | |- |_, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
  tryif
    eapply eval_tuple_ex with (i := num);
    match goal with
    | |- _ < _ => tryif simpl; lia then idtac else fail 2
    | _ => idtac
    end;
    unfold_list2;
    unfold_elements;
    solve_inners
  then
    idtac
  else
    tuple_exception_solver (S num)
  end
with
app_param_exception_solver num :=
  match goal with
  | |- |_, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_app_param_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; lia then idtac else fail 2
      | _ => idtac
      end;
      unfold_list2;
      unfold_elements;
      solve_inners
    then
      idtac
    else
      app_param_exception_solver (S num)
  end
with
call_exception_solver num :=
  match goal with
  | |- |_, _, _, _| -e> | _, inl _, _ | => fail 1
  | _ =>
    tryif
      eapply eval_call_ex with (i := num);
      match goal with
      | |- _ < _ => tryif simpl; lia then idtac else fail 2
      | _ => idtac
      end;
      unfold_list2;
      unfold_elements;
      solve_inners
    then
      idtac
    else
      call_exception_solver (S num)
  end
.

Example exp1 := ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "Y"%string (ELit (Integer 5)) (EVar "Y"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ECall "+"%string [EVar "X"%string; EVar "X"%string])))))))))))))))))))))))))))))))))))).

Goal exists id' res eff', |[], 0, exp1, []| -e> |id', res, eff'|.
Proof.
  unfold exp1. eexists. eexists. eexists.
  match goal with
  | |- ?A => assert A
  end. solve. simpl. solve.
Qed.

End Tactic.
