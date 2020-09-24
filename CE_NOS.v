Require Export CE_Aux.

Import ListNotations.

(** End of tests *)

Reserved Notation "| env , id , e , eff | -e> | id' , e' , eff' |" (at level 70).
Inductive eval_expr : Environment -> nat -> Expression -> SideEffectList -> nat -> Value + Exception -> SideEffectList -> Prop :=

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
  |insert_value env (inl v) val, id', e2, eff'| -e> |id'', res, eff''|
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
(* try 2x *)
| eval_try (env: Environment) (v1 : Var) (vl2 : list Var) (e1 e2 e3 : Expression) (res : Value + Exception) (val : Value) (eff1 eff2 eff3 : SideEffectList) (id id' id'' : nat) :
  |env, id, e1, eff1| -e> | id', inl val, eff2| ->
  |insert_value env (inl v1) val, id', e2, eff2 | -e> | id'', res, eff3|
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

Check eval_expr_ind.

Open Scope string_scope.

Example div_expr_example : Expression :=
  ELetRec ("f", 0) [] (ELet "X" (ECall "fwrite" [ELit (Atom "a")]) 
                         (EApp (EFunId ("f", 0)) []))
       (EApp (EFunId ("f", 0)) []).

(** Based on Coinductive big-step operational semantics by Leroy and Grall: *)
CoInductive InfSideEffectList :=
| ISEList (id : SideEffectId * list Value) (xs : InfSideEffectList).

Infix ":::" := ISEList (at level 60, right associativity).

Fixpoint append_to_inf (t1: SideEffectList) (t2: InfSideEffectList) {struct t1} : InfSideEffectList :=
match t1 with
| nil => t2
| e :: t => e ::: (append_to_inf t t2)
end.

Notation "a +++ b" := (append_to_inf a b) (at level 55, right associativity).

CoInductive InfSideEffectList_sim: InfSideEffectList -> InfSideEffectList -> Prop :=
| InfSideEffectList_sim_intro: forall a t1 t2,
    InfSideEffectList_sim t1 t2 -> InfSideEffectList_sim (a ::: t1) (a ::: t2).

Notation "x == y" := (InfSideEffectList_sim x y) (at level 70, no associativity).

Lemma InfSideEffectList_sim_refl: forall x, x == x.
Proof.
  cofix COINDHYP; intro. destruct x. constructor. apply COINDHYP.
Qed.

Lemma InfSideEffectList_sim_sym: forall x y, x == y -> y == x.
Proof.
  cofix COINDHYP; intros. inversion H. constructor. apply COINDHYP; auto.
Qed.

Lemma InfSideEffectList_sim_trans: forall x y z, x == y -> y == z -> x == z.
Proof.
  cofix COINDHYP; intros. inversion H; subst. inversion H0; subst. constructor. apply COINDHYP with t2; auto.
Qed.

Import List.

Lemma InfSideEffectList_app_assoc: forall (t1 t2 : SideEffectList) t3, (t1 ++ t2) +++ t3 = t1 +++ (t2 +++ t3).
Proof.
  induction t1; simpl; intros. auto. rewrite IHt1. auto.
Qed.

Lemma decompose_InfSideEffectList:
  forall t, t = match t with ISEList e t' => ISEList e t' end.
Proof.
  intro. destruct t; auto.
Qed.

Theorem inf_deconstruct e l :
  e:::l = [e] +++ l.
Proof.
  simpl. reflexivity.
Qed.

Ltac dec x := rewrite (decompose_InfSideEffectList x); simpl.

Reserved Notation "| env , id , e , eff | -i>  eff' " (at level 70).
CoInductive div_expr : Environment -> nat -> Expression -> SideEffectList -> InfSideEffectList -> Prop :=
(* Tuple *)
(* | div_tuple (env: Environment) (exps : list Expression) (vals : list Value) 
     (eff1 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) (i : nat) (eff2 eff3 : InfSideEffectList) :
  i < length exps ->
  length vals = i ->
  length eff = i ->
  length ids = i ->
  (forall j, j < i ->
    |env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j|
   -e>
    |nth_def ids id 0 (S j), inl (nth j vals ErrorValue), nth_def eff eff1 [] (S j)|) ->
  eff3 = last eff eff1 +++ eff2 ->
  |env, last ids id, nth i exps ErrorExp, last eff eff1| -i> eff3
->
  |env, id, ETuple exps, eff1| -i> eff3 *)

(* apply *)
| div_app (params : list Expression) (vals : list Value) (env : Environment) 
     (exp : Expression) (body : Expression) (var_list : list Var) 
     (ref : Environment) (ext : list (nat * FunctionIdentifier * FunctionExpression)) (n : nat)
     (eff1 eff2 : SideEffectList) (eff : list SideEffectList) (ids : list nat) (id id' : nat) (eff3 eff4 : InfSideEffectList):
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
  eff4 = last eff eff2 +++ eff3 ->
  |append_vars_to_env var_list vals (get_env ref ext), 
   last ids id',
   body, 
   last eff eff2|
  -i>
   eff4
->
  |env, id, EApp exp params, eff1| -i> eff4

(* letrec *)
| div_letrec (env: Environment) (e b : Expression) (l : list Var) (eff1 : SideEffectList) (eff2 eff3 : InfSideEffectList) (f : FunctionIdentifier) (id : nat) :
  eff3 = eff1 +++ eff2 ->
  |append_funs_to_env [(f, (l, b))] env id, S id, e, eff1| -i> eff3

->
  |env, id, ELetRec f l b e, eff1| -i> eff3

(* let *)
| div_let (env: Environment) (v : Var) (val : Value) (e1 e2 : Expression)  (eff1 eff' : SideEffectList) (id id' : nat) (eff2 eff3 : InfSideEffectList ) :
  |env, id, e1, eff1| -e> |id', inl val, eff'| ->
  eff3 = eff' +++ eff2 ->
  |insert_value env (inl v) val, id', e2, eff'| -i> eff3
->
  |env, id, ELet v e1 e2, eff1| -i> eff3
where "| env , id , e , eff | -i>  eff' " := (div_expr env id e eff eff').

CoFixpoint inf_trace1 := (Output, [VLit (Atom "a")]) ::: inf_trace1.

Lemma alma eff:
| [], 0,
   ELetRec ("f", 0) []
     (ELet "X" (ECall "fwrite" [ELit (Atom "a")]) (EApp (EFunId ("f", 0)) []))
     (EApp (EFunId ("f", 0)) []), eff ++ [(Output, [VLit (Atom "a")])] | -i>
   (eff ++ [(Output, [VLit (Atom "a")])]) +++ inf_trace1
   ->
   | [(inr ("f", 0),
   VClos []
     [(0, ("f", 0),
      ([], ELet "X" (ECall "fwrite" [ELit (Atom "a")]) (EApp (EFunId ("f", 0)) [])))] 0 []
     (ELet "X" (ECall "fwrite" [ELit (Atom "a")]) (EApp (EFunId ("f", 0)) [])));
  (inl "X", ok)], 1, EApp (EFunId ("f", 0)) [],
(eff ++ [(Output, [VLit (Atom "a")])]) ++ [(Output, [VLit (Atom "a")])] | -i>
(eff ++ [(Output, [VLit (Atom "a")])]) +++ inf_trace1.
Proof.
  intros.
  inversion H. subst. unfold append_funs_to_env in H9. simpl in H9.
  inversion H9. subst. apply eq_sym, length_zero_iff_nil in H2. apply eq_sym, length_zero_iff_nil in H5.  apply eq_sym, length_zero_iff_nil in H6. subst.
  inversion H3. simpl in H5. inversion H5. subst. clear H5.
  inversion H15. subst. inversion H10. subst.
  pose (element_exist _ _ H2).
  pose (element_exist _ _ H5).
  pose (element_exist _ _ H6).
  inversion e. inversion e0. inversion e1.
  inversion H0. inversion H1. inversion H13. subst.
  clear e. clear e0. clear e1.
  inversion H2. inversion H5. inversion H6.
  apply eq_sym, length_zero_iff_nil in H19. apply eq_sym, length_zero_iff_nil in H20.
  apply eq_sym, length_zero_iff_nil in H21. subst.
  pose (H11 0 Nat.lt_0_1). simpl in e. inversion e.
  subst.
  simpl in H16. inversion H18. subst.
  exact H16.
Qed.

(* Goal
  forall eff, | [], 0, div_expr_example, eff| -i> eff +++ inf_trace1.
Proof.
  cofix INDFIX.
  intros. unfold div_expr_example in *.
  eapply div_letrec with (eff2 := inf_trace1); auto. unfold append_funs_to_env. simpl.
  intros.
  eapply div_app with (vals := []) (eff := []) (ids := []); auto.
  * apply eval_funid. reflexivity.
  * auto.
  * intros. inversion H.
  * simpl. reflexivity.
  * simpl. eapply div_let.
    - unfold get_env. simpl. eapply eval_call with (vals := [VLit (Atom "a")]) (ids := [1]) (eff := [eff]); auto.
      + intros. inversion H. 2: inversion H1. simpl. apply eval_lit.
      + simpl. reflexivity.
    - dec inf_trace1. rewrite inf_deconstruct. instantiate (1 := inf_trace1).
      rewrite InfSideEffectList_app_assoc. reflexivity.
    - simpl.
      pose (INDFIX (eff ++ [(Output, [VLit (Atom "a")])])).
  {
  eapply div_app with (vals := []) (eff := []) (ids := []); auto.
  * apply eval_funid. reflexivity.
  * auto.
  * intros. inversion H.
  * simpl. dec inf_trace1. rewrite inf_deconstruct. rewrite InfSideEffectList_app_assoc. reflexivity.
  * simpl. eapply div_let.
    - unfold get_env. simpl. eapply eval_call with (vals := [VLit (Atom "a")]) (ids := [1]) (eff := [eff ++ [(Output, [VLit (Atom "a")])]]); auto.
      + intros. inversion H. 2: inversion H1. apply eval_lit.
      + simpl. reflexivity.
    - dec inf_trace1. dec inf_trace1. rewrite inf_deconstruct. 
      instantiate (1 := inf_trace1).
      repeat (rewrite InfSideEffectList_app_assoc). reflexivity.
    - simpl. dec inf_trace1. rewrite inf_deconstruct. rewrite <- InfSideEffectList_app_assoc.
      apply alma. assumption.
  }
Qed.
*)
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
| |- | ?env, ?id, ELit ?lit, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EVar ?v, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EFunId ?fid, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
| |- | ?env, ?id, EFun ?pl ?b, ?eff | -e> | ?id', ?res, ?eff'| => finishing_tactic
(* | |- | ?env, ?id, ETuple ?l, ?eff | -e> | ?id', ?res, ?eff'| =>
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
      solve_inners) *)
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
(* with
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
  end *)
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


Section determinism_proof.

Ltac empty_list_in_hypo :=
match goal with
| [H : 0 = length _ |- _ ] => apply eq_sym, length_zero_iff_nil in H
| [H : length _ = 0 |- _ ] => apply length_zero_iff_nil in H
| _ => idtac
end.

Ltac single_unfold_list :=
match goal with
| [ Hyp : Datatypes.length ?l = 0 |- _] => apply length_zero_iff_nil in Hyp; subst
| [ Hyp : 0 = Datatypes.length ?l |- _] => apply eq_sym, length_zero_iff_nil in Hyp; subst
| [ Hyp : Datatypes.length ?l = S ?n |- _] => symmetry in Hyp; single_unfold_list
| [ Hyp : S ?n = Datatypes.length ?l |- _] => 
   pose (element_exist _ _ Hyp);
   match goal with
   | [H' : exists x l', _ = x::l' |- _] => 
     inversion H';
     match goal with
     | [H'' : exists l', _ = ?x::l' |- _] => inversion H''; subst; simpl in Hyp; inversion Hyp
     end
   end
end
.

Lemma restrict_helper {env : Environment} {eff1 : SideEffectList} {exps : list Expression} 
    (a : Expression) (x1 : SideEffectList) (x6 : list SideEffectList) (x0 : Value) 
    (x3 : list Value) (id' : nat) (ids : list nat) (id : nat):
(forall i : nat,
    i < Datatypes.length (a :: exps) ->
    | env, nth_def (id'::ids) id 0 i, nth i (a :: exps) ErrorExp, nth_def (x1 :: x6) eff1 [] i | -e>
    | nth_def (id'::ids) id 0 (S i), inl (nth i (x0 :: x3) ErrorValue), nth_def (x1 :: x6) eff1 [] (S i) |)
->
forall i : nat,
    i < Datatypes.length exps ->
    | env, nth_def ids id' 0 i, nth i exps ErrorExp, nth_def x6 x1 [] i | -e>
    | nth_def ids id' 0 (S i), inl (nth i x3 ErrorValue), nth_def x6 x1 [] (S i) |
.
Proof.
  intros.
  assert (S i < Datatypes.length (a :: exps)) as A1.
  { simpl. lia. } pose (E := H (S i) A1). 
  (* pose (P1 := @concatn_app eff1 x1 x6 i).
  pose (P2 := @concatn_app eff1 x1 x6 (S i)).
  rewrite P1, P2 in E. *) simpl in E. simpl. unfold nth_def. exact E.
Qed.

Lemma list_equality {env : Environment} {exps : list Expression} {eff1 : SideEffectList} : 
forall vals vals0 : list Value, forall eff eff4 : list SideEffectList,
forall id ids ids0,
  (forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i | 
     -e> 
     | nth_def ids id 0 (S i), inl (nth i vals ErrorValue), nth_def eff eff1 [] (S i) |)
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i |
     -e>
     | id'', v2, eff'' | ->
     inl (nth i vals ErrorValue) = v2 /\ nth_def eff eff1 [] (S i) = eff'' /\ nth_def ids id 0 (S i) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_def ids0 id 0 i, nth i exps ErrorExp, nth_def eff4 eff1 [] i |
     -e> 
     | nth_def ids0 id 0 (S i), inl (nth i vals0 ErrorValue), nth_def eff4 eff1 [] (S i) |)
->
Datatypes.length exps = Datatypes.length vals0
->
Datatypes.length exps = Datatypes.length eff4
->
Datatypes.length exps = Datatypes.length vals
->
Datatypes.length exps = Datatypes.length eff
->
length exps = length ids
->
length exps = length ids0
->
eff = eff4 /\ vals = vals0 /\ ids = ids0.
Proof.
  generalize dependent eff1. induction exps.
  * intros. simpl in H3, H2, H4, H5, H6, H7.
    repeat (empty_list_in_hypo).
    subst. auto.
  * intros. inversion H3. inversion H2. inversion H4. inversion H5. inversion H6. inversion H7.
  
  (* first elements are the same *)
    single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list.
    single_unfold_list. single_unfold_list.
    pose (P1 := H1 0 list_length).
    pose (P2 := H0 0 list_length (inl x7) (nth_def (x9 :: x10) eff1 [] 1) x).
    pose (P3 := P2 P1). inversion P3. inversion H25. inversion H27. simpl in H28. simpl in H30.
    subst.
  (* remaining lists are the same *)

  (* These three asserts ensure, that if something states for every element in 
    a (b::l) list, then it states for every element in l too*)
    assert (
      (forall i : nat,
    i < Datatypes.length exps ->
    | env, nth_def x2 x 0 i, nth i exps ErrorExp, nth_def x4 x9 [] i | -e> 
    | nth_def x2 x 0 (S i), inl (nth i x6 ErrorValue),
    nth_def x4 x9 [] (S i) |)
    ).
    {
      intros. pose (P4 := restrict_helper a _ _ _ _ _ _ _ H i H28). assumption.
    }
    assert (
      (forall i : nat,
      i < Datatypes.length exps ->
      forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
      | env, nth_def x2 x 0 i, nth i exps ErrorExp, nth_def x4 x9 [] i | -e> | id'', v2, eff'' | ->
      inl (nth i x6 ErrorValue) = v2 /\ nth_def x4 x9 [] (S i) = eff'' /\ nth_def x2 x 0 (S i) = id'')
    ).
    {
      intros. assert (S i < Datatypes.length (a::exps)). { simpl. lia. } 
      pose (P4 := H0 (S i) H31 v2 eff'' id''). simpl nth in P4. exact (P4 H30).
    }
    assert (
     (forall i : nat,
    i < Datatypes.length exps ->
    | env, nth_def x0 x 0 i, nth i exps ErrorExp, nth_def x10 x9 [] i | -e>
    | nth_def x0 x 0 (S i), inl (nth i x8 ErrorValue),
    nth_def x10 x9 [] (S i) |)
    ).
    {
      intros. assert (S i < Datatypes.length (a :: exps)). { simpl. lia. } 
      pose (P4 := H1 (S i) H31). simpl nth in P4. assumption.
    }
    (* simpl list lengths *)
    inversion H10. inversion H11. inversion H12. inversion H13. inversion H14.
    pose (IH := IHexps x9 x6 x8 x4 x10 x x2 x0 H28 H29 H30 H32 H26 H33 H34 H35 H36). 
    inversion IH. inversion H37. subst. auto.
Qed.

Lemma firstn_eq {env : Environment} {eff : list SideEffectList} : 
forall (eff5 : list SideEffectList) (exps : list Expression) (vals vals0 : list Value) 
   (eff1 : SideEffectList) (ids ids0 : list nat) (id id'' : nat) ex eff3,
length exps = length vals ->
Datatypes.length exps = Datatypes.length eff
->
Datatypes.length eff5 = Datatypes.length vals0
->
Datatypes.length vals0 < Datatypes.length exps 
->
length exps = length ids
->
length ids0 = length vals0
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i | -e> | id'', v2, eff'' | ->
     inl (nth i vals ErrorValue) = v2 /\ nth_def eff eff1 [] (S i) = eff'' /\ nth_def ids id 0 (S i) = id'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff5 eff1 [] j | -e>
     | nth_def ids0 id 0 (S j), inl (nth j vals0 ErrorValue),
     nth_def eff5 eff1 [] (S j) |)
->
| env, last ids0 id, nth (Datatypes.length vals0) exps ErrorExp,
      last eff5 eff1 | -e> | id'', inr ex,
      eff3 |
->
False.
Proof.
  induction eff.
  * intros. inversion H0. rewrite H9 in H2. inversion H2.
  * intros. destruct eff5.
    - inversion H1. simpl in H1. apply eq_sym, length_zero_iff_nil in H1. subst.
      simpl in H4.
      apply length_zero_iff_nil in H4. subst. simpl in H0. rewrite H0 in H5.
      pose (P := H5 0 (Nat.lt_0_succ _) _ _ _ H7). destruct P. inversion H1.
    - inversion H1. simpl.
    (* first elements *)
      inversion H0.
      assert (0 < length exps). { lia. }
      assert (0 < length vals0). { lia. }
      assert (0 < length ids0). { lia. }
      simpl in H0, H1.
      (* single_unfold_list H1. *)
      assert (Datatypes.length exps = S (Datatypes.length eff)) as Helper. { auto. }
      assert (Datatypes.length ids0 = Datatypes.length vals0) as Helper2. { auto. }
      assert (Datatypes.length exps = Datatypes.length ids) as Helper3. { auto. }
      pose (EE1 := element_exist _ _ (eq_sym H10)).
      pose (EE2 := element_exist _ _ H1).
      rewrite H in H0.
      pose (EE3 := element_exist _ _ (eq_sym H0)).
      rewrite <- H1 in H4. rewrite H10 in H3.
      pose (EE4 := element_exist _ _ H3).
      pose (EE5 := element_exist _ _ (eq_sym H4)).
      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v'].
      inversion EE4 as [id0']. inversion EE5 as [id0'']. 
      inversion H13. inversion H14. inversion H15. inversion H16. inversion H17. subst.
      pose (P0 := H6 0 H11).
      pose (P1 := H5 0 H8 (inl v) (s)).
      pose (P2 := P1 _ P0). destruct P2. destruct H18, H19. simpl in H18, H19. subst.
    (* other elements *)
      inversion H1.
      eapply IHeff with (exps := x) (vals := x1) (vals0 := x0) (eff1 := s)
                      (ids := x2) (ids0 := x3) (id := id0'') (eff5 := eff5); auto.
        + intuition.
        + intros. assert (S i < Datatypes.length (e :: x)). { simpl. lia. }
          pose (A := H5 (S i) H21 v2 eff''). simpl in A, H20.
          pose (B := A _ H20). assumption.
        + intros. assert (S j < Datatypes.length (v :: x0)). { lia. } 
          pose (A := H6 (S j) H20). exact A.
        + rewrite <- last_element_equal, <- last_element_equal in H7. exact H7.
Qed.

(** Side effect equality until the ith element using concatn *)
Lemma eff_until_i {env : Environment} {eff : list SideEffectList} : 
forall (eff5 : list SideEffectList) {exps : list Expression} (vals vals0 : list Value) 
   (eff1 : SideEffectList) (ids ids0 : list nat) (id id'' : nat) ex  eff3,
length exps = length vals ->
Datatypes.length exps = Datatypes.length eff
->
Datatypes.length eff5 = Datatypes.length vals0
->
Datatypes.length vals0 < Datatypes.length exps 
->
length exps = length ids
->
length ids0 = length vals0
->
(forall i : nat,
     i < Datatypes.length exps ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 i, nth i exps ErrorExp, nth_def eff eff1 [] i | -e> | id'', v2, eff'' | ->
     inl (nth i vals ErrorValue) = v2 /\ nth_def eff eff1 [] (S i) = eff'' /\ nth_def ids id 0 (S i) = id'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff5 eff1 [] j | -e>
     | nth_def ids0 id 0 (S j), inl (nth j vals0 ErrorValue),
     nth_def eff5 eff1 [] (S j) |)
->
| env, last ids0 id, nth (Datatypes.length vals0) exps ErrorExp,
      last eff5 eff1 | -e> | id'', inr ex, eff3 |
->
  False.
Proof.
  intros. pose (P := firstn_eq eff5 exps vals vals0 _ _ _ _ _ _ _
                                H H0 H1 H2 H3 H4 H5 H6 H7). inversion P.
Qed.


Lemma firstn_eq_rev {env : Environment} {eff : list SideEffectList} : 
   forall (eff5 : list SideEffectList) (exps : list Expression) (vals vals0 : list Value) 
          (eff1 : SideEffectList) (ids ids0 : list nat) (id : nat) (eff2 : SideEffectList) 
          (id' : nat) (ex : Exception),
(forall j : nat,
     j < Datatypes.length vals ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
     inl (nth j vals ErrorValue) = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_def ids0 id 0 i, nth i exps ErrorExp, nth_def eff5 eff1 [] i | -e>
     | nth_def ids0 id 0 (S i), inl (nth i vals0 ErrorValue),
     nth_def eff5 eff1 [] (S i) |) ->
(forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
        | env, last ids id, nth (Datatypes.length vals) exps ErrorExp,
        last eff eff1 | -e> | id'', v2, eff'' | ->
        inr ex = v2 /\ eff2 = eff'' /\ id' = id'')
->
Datatypes.length vals < Datatypes.length exps ->
Datatypes.length eff = Datatypes.length vals ->
Datatypes.length exps = Datatypes.length vals0 ->
Datatypes.length exps = Datatypes.length eff5 ->
length exps = length ids0 ->
length ids = length vals
->
False.
Proof.
  induction eff.
  * intros. apply eq_sym, length_zero_iff_nil in H3. subst.
    apply length_zero_iff_nil in H7. subst.
    pose (P := H0 0 H2).
    pose (P2 := H1 _ _ _ P). inversion P2. congruence.
  * intros. destruct eff5.
    - inversion H5. rewrite H5 in H2. inversion H2.
    - inversion H3. inversion H5.
    (* first elements *)
      assert (0 < length exps). { lia. } assert (0 < length vals). { lia. }
      assert (S (Datatypes.length eff5) = Datatypes.length exps). { auto. }
      assert (Datatypes.length exps = Datatypes.length vals0) as LENGTH. { auto. }
      assert (S (Datatypes.length eff) = Datatypes.length vals) as Helper1. { auto. }
      assert (Datatypes.length exps = Datatypes.length ids0) as Helper2. { auto. }
      (* single_unfold_list H9. *)
      pose (EE1 := element_exist (length eff5) exps (eq_sym H5)).
      pose (EE2 := element_exist (length eff) vals H9).
      rewrite H5 in H4, H6. rewrite <- H9 in H7.
      pose (EE3 := element_exist (length eff5) vals0 H4).
      pose (EE4 := element_exist _ _ (eq_sym H7)).
      pose (EE5 := element_exist _ _ H6).
      
      inversion EE1 as [e]. inversion EE2 as [v]. inversion EE3 as [v'].
      inversion EE4 as [id0']. inversion EE5 as [id0'']. 
      inversion H13. inversion H14. inversion H15. inversion H16. inversion H17. subst.
      pose (P0 := H0 0 H8).
      pose (P1 := H 0 H11 (inl v') s).
      pose (P2 := P1 _ P0). destruct P2. destruct H19. inversion H18. simpl in H19, H20. subst.
    (* other elements *)
      inversion H3.
      apply IHeff with (exps := x) (vals := x0) (eff1 := s) (vals0 := x1)
                  (ids := x2) (ids0 := x3) (id := id0'') (ex := ex) (eff5 := eff5)
                  (eff2 := eff2) (id' := id'); auto.
        + intros. assert (S j < Datatypes.length (v' :: x0)). { simpl. lia. } 
          pose (A := H (S j) H22 v2 eff'').
          pose (B := A _ H21). assumption.
        + intros. assert (S i < Datatypes.length (e :: x)). { simpl. lia. } 
          pose (A := H0 (S i) H21). exact A.
        + intros. rewrite <- last_element_equal, <- last_element_equal in H1. apply H1. assumption.
        + intuition.
        + inversion H7. lia.
Qed.

(** First i (length vals) element are equal with concatn *)
Lemma eff_until_i_rev {env : Environment} {eff : list SideEffectList} : 
   forall (eff5 : list SideEffectList) (exps : list Expression) (vals vals0 : list Value) 
          (eff1 : SideEffectList) (ids ids0 : list nat) (id : nat) (eff2 : SideEffectList) 
          (id' : nat) (ex : Exception),
(forall j : nat,
     j < Datatypes.length vals ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
     inl (nth j vals ErrorValue) = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall i : nat,
     i < Datatypes.length exps ->
     | env, nth_def ids0 id 0 i, nth i exps ErrorExp, nth_def eff5 eff1 [] i | -e>
     | nth_def ids0 id 0 (S i), inl (nth i vals0 ErrorValue),
     nth_def eff5 eff1 [] (S i) |) ->
(forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
        | env, last ids id, nth (Datatypes.length vals) exps ErrorExp,
        last eff eff1 | -e> | id'', v2, eff'' | ->
        inr ex = v2 /\ eff2 = eff'' /\ id' = id'')
->
Datatypes.length vals < Datatypes.length exps ->
Datatypes.length eff = Datatypes.length vals ->
Datatypes.length exps = Datatypes.length vals0 ->
Datatypes.length exps = Datatypes.length eff5 ->
length exps = length ids0 ->
length ids = length vals
->
False.
Proof.
  intros. apply (firstn_eq_rev eff5 exps vals vals0 eff1 _ _ _ _ _ _
                                   H H0 H1 H2 H3 H4 H5 H6 H7).
Qed.

Lemma con_n_equality {env : Environment} {eff : list SideEffectList} : 
  forall (exps : list Expression) (vals vals0 : list Value) eff1 eff6 i i0 ids ids0 id eff3 id' ex,
(forall j : nat,
    j < i ->
    forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
    inl (nth j vals ErrorValue) = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall j : nat,
     j < i0 ->
     | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -e>
     | nth_def ids0 id 0 (S j), inl (nth j vals0 ErrorValue),
     nth_def eff6 eff1 [] (S j) |)
->
(forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, last ids id, nth i exps ErrorExp, last eff eff1 | -e> | id'', v2, eff'' | ->
     inr ex = v2 /\ eff3 = eff'' /\ id' = id'')
->
Datatypes.length eff = i ->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length vals0 = i0 ->
i0 < Datatypes.length exps ->
Datatypes.length eff6 = i0 ->
length ids = i ->
length ids0 = i0 ->
i < i0
->
False.
Proof.
  induction eff.
  * intros. simpl in H1. subst. simpl in H10. pose (P := H0 0 H10).
    simpl in H8, P. apply length_zero_iff_nil in H8. subst.
    pose (P2 := H1 _ _ _ P). inversion P2. congruence.
  * intros. inversion H2. simpl in H2. rewrite <- H2 in H4.
    pose (EE1 := element_exist (length eff) vals (eq_sym H4)). 
    inversion EE1 as [v]. inversion H12 as [vs]. destruct eff6.
    - simpl in H7. subst. rewrite <- H7 in H10. inversion H10.
    - subst. simpl. (* simpl_concatn_H IHeff. rewrite concatn_app, concatn_app. simpl_concatn. *)
      simpl in H7. (* single_unfold_list H6. *) 
      pose (EE2 := element_exist (length eff6) vals0 H7). inversion EE2. 
      inversion H2.
      pose (NE := nat_lt_zero _ _  H3). inversion NE.
      pose (EE3 := element_exist x1 exps (eq_sym H13)). inversion EE3. inversion H14.
      subst. 
      pose (EE4 := element_exist _ _ (eq_sym H8)).
      pose (EE5 := element_exist _ _ (eq_sym H9)).
      inversion EE4 as [id0']. inversion EE5 as [id0''].
      inversion H5. inversion H15. subst.
      assert (s = a /\ id0' = id0''). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. lia. }
        pose (P := H0 0 H16).
        assert (0 < S (Datatypes.length eff)). {  simpl. lia. }
        pose (P2 := H 0 H17 (inl (nth 0 (x :: x0) ErrorValue)) (nth_def (s :: eff6) eff1 [] 1) _ P). 
        inversion P2.
        destruct H19. auto.
      }
      destruct H16. subst.
      
      eapply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := a)
                        (i0 := length x0) (ids := x4) (ids0 := x5); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. lia. }
        pose (P := H (S j) H18 v2 eff'' id''). pose (P H17). assumption.
      + intros. assert (S j < Datatypes.length (x :: x0)). { simpl. lia. }
        pose (P := H0 (S j) H17). exact P.
      + intros. apply H1.
        rewrite (last_element_equal _ _ id), (last_element_equal _ _ eff1) in H16.
        exact H16.
      + intuition.
      + intuition.
      + intuition.
      + intuition.
Qed.

Lemma con_n_equality_rev {env : Environment} {eff : list SideEffectList} : 
forall (exps : list Expression) (vals vals0 : list Value) (eff1 : SideEffectList) 
   (eff6 : list SideEffectList) (i i0 : nat) (id : nat) (ids ids0 : list nat) id' ex0 eff4,
(forall j : nat,
    j < i ->
    forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
    inl (nth j vals ErrorValue) = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall j : nat,
     j < i0 ->
     | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -e> 
     | nth_def ids0 id 0 (S j), inl (nth j vals0 ErrorValue),
     nth_def eff6 eff1 [] (S j) |)
->
Datatypes.length eff = i ->
i < Datatypes.length exps ->
Datatypes.length vals = i ->
Datatypes.length vals0 = i0 ->
i0 < Datatypes.length exps ->
Datatypes.length eff6 = i0 ->
length ids = i ->
length ids0 = i0 ->
i > i0 ->
(| env, last ids0 id, nth i0 exps ErrorExp, last eff6 eff1 | -e> | id', 
     inr ex0,eff4 |)
->
False.
Proof.
induction eff.
  * intros. simpl in H1. subst. inversion H9.
  * intros. simpl in H1. rewrite <- H1 in H3.
    pose (EE1 := element_exist (length eff) vals (eq_sym H3)).
    inversion EE1 as [v]. inversion H11 as [vs]. destruct eff6.
    - subst. apply eq_sym, length_zero_iff_nil in H6. subst. apply length_zero_iff_nil in H8.
      subst.
      simpl in H10. pose (P := H 0 (Nat.lt_0_succ _) _ _ _ H10). inversion P. congruence.
    - subst.
      assert (Datatypes.length ids0 = Datatypes.length vals0) as Helper. { auto. }
      pose (EE2 := element_exist (length eff6) vals0 H6). inversion EE2. inversion H1.
      pose (NE := nat_lt_zero _ _ H2). inversion NE.
      pose (EE3 := element_exist x1 exps (eq_sym H12)). inversion EE3.
      inversion H13. subst.
      pose (EE4 := element_exist _ _ (eq_sym H7)).
      pose (EE5 := element_exist _ _ (eq_sym H8)).
      inversion EE4 as [id0']. inversion EE5 as [id0'']. inversion H4. inversion H14. subst.
      assert (s = a /\ id0' = id0''). {
        subst.
        assert (0 < Datatypes.length (x :: x0)). {  simpl. lia. }
        pose (P := H0 0 H15).
        assert (0 < S (Datatypes.length eff)). {  simpl. lia. }
        pose (P1 := H 0 H16 (inl (nth 0 (x :: x0) ErrorValue)) (nth_def (s :: eff6) eff1 [] 1) _ P).
        destruct P1. destruct H18. simpl in H19, H18. auto.
      }
      destruct H15. subst.
      eapply IHeff with (exps := x3) (vals := vs) (vals0 := x0) (eff1 := a) 
                       (i0 := length eff6) (i := length eff) (ids := x4) (ids0 := x5); auto.
      + intros. assert (S j < S (Datatypes.length eff)). { simpl. lia. }
        pose (P := H (S j) H17 v2 eff''). simpl in P.
        pose (P1 := P _ H16). assumption.
      + intros. inversion H6. assert (S j < Datatypes.length (x :: x0)). { simpl. lia. }
        pose (P := H0 (S j) H16). assumption.
      + intuition.
      + inversion H6. auto.
      + rewrite <- H6 in H5. simpl in H5. lia.
      + rewrite <- H6 in Helper. auto.
      + simpl in *. rewrite <- H6 in H9. lia.
      + rewrite <- last_element_equal, <- last_element_equal in H10. simpl in H10. 
        inversion H6. rewrite H16. exact H10.
Qed.


Lemma list_equal_until_i {env : Environment} {eff : list SideEffectList} :
  forall (exps : list Expression) (vals vals0 : list Value) (eff6 : list SideEffectList)
      (eff1 : SideEffectList) (ids ids0 : list nat) (id : nat),
(forall j : nat,
    j < Datatypes.length vals ->
    forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
    | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
    inl (nth j vals ErrorValue) = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
(forall j : nat,
     j < Datatypes.length vals0 ->
     | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -e> 
     | nth_def ids0 id 0 (S j), inl (nth j vals0 ErrorValue),
     nth_def eff6 eff1 [] (S j) |)
->
Datatypes.length vals = Datatypes.length vals0
->
Datatypes.length eff = Datatypes.length vals
->
Datatypes.length eff6 = Datatypes.length vals0
->
Datatypes.length vals0 < Datatypes.length exps
->
length ids = length vals
->
length ids0 = length vals0
->
eff = eff6 /\ vals = vals0 /\ ids = ids0.
Proof.
  induction eff.
  * intros. inversion H2. apply eq_sym, length_zero_iff_nil in H8. subst. simpl in H1. 
    apply eq_sym, length_zero_iff_nil in H1. subst. simpl in H3. apply length_zero_iff_nil in H3. 
    apply length_zero_iff_nil in H5. apply length_zero_iff_nil in H6. subst. auto.
  * intros. simpl in H2. rewrite <- H2 in H1. rewrite <- H1 in H3. pose (NE := nat_lt_zero _ _ H4). inversion NE.
    (* single_unfold_list H2. *)
    pose (EE1 := element_exist (length eff) vals H2).
    pose (EE2 := element_exist (length eff) vals0 H1).
    pose (EE3 := element_exist (length eff) eff6 (eq_sym H3)).
    pose (EE4 := element_exist x exps (eq_sym H7)).
    inversion EE1 as [v]. inversion EE2 as [v']. inversion EE3 as [fe]. inversion EE4 as [e'].
    inversion H8. inversion H9. inversion H10. inversion H11. subst.
    pose (EE5 := element_exist _ _ (eq_sym H5)).
    pose (EE6 := element_exist _ _ (eq_sym H6)).
    inversion EE5 as [id']. inversion EE6 as [id''].
    inversion H12. inversion H13. subst.
    assert (0 < Datatypes.length (v' :: x1)). { simpl. lia. }
    pose (P := H0 0 H14).
    assert (0 < Datatypes.length (v :: x0)). { simpl. lia. }
    pose (P1 := H 0 H15 (inl (nth 0 (v' :: x1) ErrorValue)) (nth_def (fe :: x2) eff1 [] 1) _ P).
    inversion P1. destruct H17. simpl in H18. inversion H16. simpl in H17. subst.
    
    assert (eff = x2 /\ x0 = x1 /\ x4 = x5).
    {
      apply IHeff with (exps := x3) (vals := x0) (vals0 := x1) (eff1 := fe) (id := id''); auto.
      + intros. assert (S j < S (Datatypes.length x0)). { simpl. lia. } pose (P2 := H (S j) H19 v2 eff''). 
        simpl in P2. pose (P2 _ H18). assumption.
      + intros. assert (S j < Datatypes.length (v' :: x1)). { simpl. lia. }
        pose (P3 := H0 (S j) H18). simpl in P3. assumption.
      + inversion H2. inversion H3. inversion H1. auto.
      + inversion H2. inversion H3. inversion H1. auto.
      + intuition.
    }
    inversion H17. inversion H19. subst. auto.
Qed.

Lemma exception_equality {env : Environment} {exps : list Expression} (vals vals0 : list Value) 
   (ex : Exception) (eff1 : SideEffectList) (eff eff6 : list SideEffectList) (i i0 : nat) 
   (eff3 : SideEffectList) (ex0 : Exception) (eff4 : SideEffectList) (ids ids0 : list nat)
   (id id' id'' : nat) :
(forall j : nat,
     j < i ->
     forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
     | env, nth_def ids id 0 j, nth j exps ErrorExp, nth_def eff eff1 [] j | -e> | id'', v2, eff'' | ->
     inl (nth j vals ErrorValue) = v2 /\ nth_def eff eff1 [] (S j) = eff'' /\ nth_def ids id 0 (S j) = id'')
->
| env, last ids0 id, nth i0 exps ErrorExp, last eff6 eff1 | -e>
| id'', inr ex0, eff4 |
->
(forall (v2 : Value + Exception) (eff'' : SideEffectList) (id'' : nat),
        | env, last ids id, nth i exps ErrorExp, last eff eff1 | -e>
        | id'', v2, eff'' | -> inr ex = v2 /\ eff3 = eff'' /\ id' = id'')
->
(forall j : nat,
      j < i0 ->
      | env, nth_def ids0 id 0 j, nth j exps ErrorExp, nth_def eff6 eff1 [] j | -e>
      | nth_def ids0 id 0 (S j), inl (nth j vals0 ErrorValue),
      nth_def eff6 eff1 [] (S j) |)
->
Datatypes.length vals = i ->
 i < Datatypes.length exps ->
 Datatypes.length eff = i ->
 Datatypes.length vals0 = i0 ->
 i0 < Datatypes.length exps ->
 Datatypes.length eff6 = i0 ->
 length ids = i ->
 length ids0 = i0
->
i = i0 /\ eff = eff6 /\ vals = vals0 /\ ids = ids0.
Proof.
  intros.
  destruct (Compare_dec.le_gt_dec i i0).
  * case_eq (Lt.le_lt_or_eq i i0 l).
    - intros.
      pose (P1 := con_n_equality exps vals vals0 eff1 eff6 i i0 ids ids0 id _ _ _
                 H H2 H1 H5 H4 H3 H6 H7 H8 H9 H10 l0). inversion P1.
    - intros. subst. pose (list_equal_until_i exps vals vals0 eff6 eff1 _ _ _
                            H H2 e H5 H8 H7 H9 H10). auto.
  * pose (P := con_n_equality_rev exps vals vals0 eff1 eff6 i i0 id ids ids0 _ _ _
               H H2 H5 H4 H3 H6 H7 H8 H9 H10 g H0). inversion P.
Qed.

Theorem nos_determinism : forall {env : Environment} {e : Expression} {v1 : Value + Exception} 
    {id id' : nat} {eff eff' : SideEffectList}, 
  |env, id, e, eff| -e> | id', v1, eff'|
->
  (forall v2 eff'' id'', |env, id, e, eff| -e> |id'', v2, eff''| -> v1 = v2 /\ eff' = eff''
      /\ id' = id'').
Proof.
  intro. intro. intro. intro. intro. intro. intro. intro IND. induction IND.
  (* LITERAL, VARIABLE, FUNCTION SIGNATURE, FUNCTION DEFINITION *)
  1-3: intros; inversion H; try(inversion H0); subst; auto.
  * intros. inversion H. auto.

  (* CALL *)
  * intros. inversion H6.
    - subst.
      pose (LEQ := list_equality vals vals0 eff eff4 _ _ _ H2 H3 H12 H9 H10 H H0 H1 H11).
      destruct LEQ. destruct H7. subst. rewrite H4 in H15. inversion H15.
      subst. auto.
    - subst. pose (P1 := H3 (Datatypes.length vals0) H9 (inr ex)
                            eff'').
      pose (EU := @eff_until_i env eff eff4 params vals vals0 eff1 _ _ id _ _ _ 
                H H0 H11 H9 H1 H12 H3 H15 H20). inversion EU.

  (* APPLY *)
  * intros. inversion H5.
    - subst. apply IHIND1 in H9. inversion H9. destruct H7.
      inversion H6. subst.
      pose (EQ := list_equality vals vals0 eff eff6 _ _ _ H3 H4 H15 H8 H11 H H1 H2 H12).
      inversion EQ. destruct H13. subst.
      apply IHIND2 in H20. destruct H20. destruct H13. auto.
    - subst. apply IHIND1 in H14. inversion H14. congruence.
    - subst. apply IHIND1 in H12. destruct H12. destruct H7.
      inversion H6. subst.
      pose (P1 := @eff_until_i env eff eff6 params vals vals0 _ _ _ _ _ _ _
                H H1 H10 H8 H2 H11 H4 H15 H20).
      inversion P1.
    - subst. apply IHIND1 in H11. inversion H11. inversion H6. subst.
      pose (P := H13 ref ext var_list body). congruence.
    - subst. apply IHIND1 in H11. inversion H11. inversion H6. subst. congruence.

  (* LET *)
  * intros. inversion H; subst.
    - apply IHIND1 in H9. destruct H9, H1. inversion H0. subst.
      apply IHIND2. auto.
    - apply IHIND1 in H9. destruct H9. congruence.

  (* LETREC *)
  * intros. inversion H. 
    - subst. apply IHIND. auto.

  (* CORECT TRY *)
  * intros. inversion H; subst.
    - apply IHIND1 in H11. destruct H11, H1. inversion H0. subst.
      apply IHIND2. auto.
    - apply IHIND1 in H11. destruct H11. congruence.

  (* CORRECT CATCH *)
  * intros. inversion H; subst.
    - apply IHIND1 in H11. destruct H11, H1. inversion H0.
    - apply IHIND1 in H11. destruct H11, H1. inversion H0. subst. apply IHIND2. auto.

  (* CALL EXCEPTION *)
  * intros. inversion H5.
    - subst.
      pose (EU := @eff_until_i_rev env eff _ params vals vals0 eff1 ids ids0 id _ _ _
              H4 H11 IHIND H H1 H8 H9 H10 H2). inversion EU.
    - apply IHIND.
      pose (EEQ := exception_equality vals vals0 ex eff1 eff _ i
             i0 _ ex0 _ _ _ _ _ _ H4 H19 IHIND H14 H0 H H1 H9 H8 H10 H2 H11).
      destruct EEQ. destruct H21. destruct H22. subst. assumption.

  (* APPLY EXCEPTION *)
  (* name evaluates to an exception *)
  * intros. inversion H.
    - subst. pose (IH := IHIND _ _ _ H3). inversion IH. congruence.
    - subst. apply IHIND. assumption.
    - subst. pose (IH := IHIND _ _ _ H6). inversion IH. congruence.
    - subst. pose (IH := IHIND _ _ _ H5). inversion IH. congruence.
    - subst. pose (IH := IHIND _ _ _ H5). inversion IH. congruence.

  (* parameter exception *)
  * intros. inversion H5.
    - subst. apply IHIND1 in H9. destruct H9. destruct H6. inversion H0.
      subst.
      pose (P1 := @eff_until_i_rev env eff _ params vals vals0 _ ids ids0 id'0 _ _ _
                   H4 H15 IHIND2 H H1 H8 H11 H12 H2). inversion P1.
    - subst. apply IHIND1 in H14. inversion H14. congruence.
    - apply IHIND1 in H12. destruct H12. destruct H21. inversion H12.
      rewrite H21, H22, H24 in *.
      assert (| env, last ids0 id'0, nth i0 params ErrorExp, last eff6 eff4 | -e> | id''0, inr ex0, eff'' |). { assumption. }
      pose (EE := exception_equality vals vals0 ex _ eff _ i i0 _ ex0
                 _ _ _ _ _ _ H4 H20 IHIND2 H15 H0 H H1 H9 H8 H10 H2 H11).
      destruct EE. destruct H26. destruct H27. subst.
      apply IHIND2 in H23.
      assumption.
    - subst. apply IHIND1 in H11. destruct H11. inversion H0. destruct H6.
      subst.
      pose (P1 := @eff_until_i_rev env eff _ params vals vals0 _ ids ids0 id'0 _ _ _
                 H4 H12 IHIND2 H H1 H8 H9 H10 H2). inversion P1.
    - subst. apply IHIND1 in H11. destruct H11. inversion H0. destruct H6.
      subst.
      pose (P1 := @eff_until_i_rev env eff _ params vals vals0 _ ids ids0 id'0 _ _ _
                 H4 H12 IHIND2 H H1 H8 H9 H10 H2). inversion P1.

  (* name evaluate to a non-closure value *)
  * intros. inversion H7.
    - apply IHIND in H11. destruct H11. destruct H23. inversion H11.
      pose (P := H4 ref ext var_list body _ H26). inversion P.
    - subst. apply IHIND in H16. inversion H16. congruence.
    - subst. apply IHIND in H14. destruct H14. inversion H5. destruct H6.
      subst.
      pose (P1 := @eff_until_i env eff _ params vals vals0 _ ids ids0 id'0 id''0 ex _
                         H H0 H12 H10 H1 H13 H3 H17 H22). inversion P1.
    - subst. apply IHIND in H13. destruct H13. inversion H5. destruct H6. subst.
      pose (LEQ := @list_equality env params _ vals vals0 eff _ _ _ _
                     H2 H3 H14 H10 H11 H H0 H1 H12).
      destruct LEQ. destruct H8. subst. auto.
    - subst. apply IHIND in H13. destruct H13. inversion H5. destruct H6. subst.
      pose (P := H4 ref ext var_list body). congruence.

  (* paramlist is too short/long *)
  * intros. inversion H7.
    - subst. 
      pose (P1 := IHIND _ _ _ H11). destruct P1. destruct H6. inversion H5. subst.
      pose (EL:= list_equality vals vals0 eff _ _ _ _ H2 H3 H17 H10 H13 H H0 H1 H14).
      destruct EL. destruct H8. subst. intuition. 
    - subst. pose (IH := IHIND _ _ _ H16). inversion IH. congruence.
    - subst.
      pose (P1 := IHIND _ _ _ H14). destruct P1. destruct H6. inversion H5. subst.
      pose (P2 := @eff_until_i env eff _ params vals vals0 _ ids ids0 id'0 id''0 ex _
                     H H0 H12 H10 H1 H13 H3 H17 H22). inversion P2.
    - subst.
      pose (P1 := IHIND _ _ _ H13). destruct P1. destruct H6. inversion H5. subst.
      pose (P2 := H15 ref ext var_list body).
      congruence.
    - subst.
      pose (P1 := IHIND _ _ _ H13). destruct P1. destruct H6. inversion H5. subst.
      pose (EL:= list_equality vals vals0 eff _ _ _ _ H2 H3 H14 H10 H11 H H0 H1 H12).
      destruct EL. destruct H8. subst. auto.

  
  (* LET EXCEPTION *)
  * intros. inversion H; subst.
    - apply IHIND in H9. destruct H9. congruence.
    - apply IHIND in H9. destruct H9. destruct H1. inversion H0. auto.
Qed.



End determinism_proof.


