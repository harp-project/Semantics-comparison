
From CE Require Export Helpers.

Import ListNotations.

Definition Environment : Type := list ((Var + FunctionIdentifier) * Value).

Fixpoint count_closures (env : Environment) : nat :=
match env with
| [] => 0
| (_, VClos _ _ _ _ _)::xs => S (count_closures xs)
| _::xs => count_closures xs
end.

(** Get *)
Fixpoint get_value (env : Environment) (key : (Var + FunctionIdentifier)) 
   : (Value + Exception) :=
match env with
| [ ] => inr novar
| (k,v)::xs => if var_funid_eqb key k then inl v else get_value xs key
end.

(** Insert *)
Fixpoint insert_value (env : Environment) (key : (Var + FunctionIdentifier)) 
   (value : Value) : Environment :=
match env with
  | [] => [(key, value)]
  | (k,v)::xs => if var_funid_eqb k key then (key,value)::xs else (k,v)::(insert_value xs key value)
end.

(** Add additional bindings *)
(** We used here: when binding, variables must be unique *)
Fixpoint add_bindings (bindings : list (Var * Value)) (env : Environment) : Environment :=
match bindings with
| [] => env
| (v, e)::xs => add_bindings xs (insert_value env (inl v) e)
end.

(** Add bindings with two lists *)
Fixpoint append_vars_to_env (vl : list Var) (el : list Value) (d : Environment) 
   : Environment :=
match vl, el with
| [], [] => d
| v::vs, e::es => append_vars_to_env vs es (insert_value d (inl v) e)
| _, _ => []
end.


Definition append_try_vars_to_env (vl : list Var) (el : list Value) (d : Environment) 
   : Environment :=
match el with
| [] => []
| e::es =>
if length vl =? 2 then append_vars_to_env vl es d else append_vars_to_env vl el d
end.


(** Not Overwriting insert *)
(** Overwriting does not fit with this recursion *)
Fixpoint insert_function (id : nat) (v : FunctionIdentifier) (p : list Var) (b : Expression) 
   (l : list (nat * FunctionIdentifier * FunctionExpression)) 
    : list (nat * FunctionIdentifier * FunctionExpression) :=
match l with
| [] => [(id, v, (p, b))]
| (id', k, v0)::xs => if funid_eqb k v then (id', k, v0)::xs 
                                   else (id', k, v0)::(insert_function id v p b xs)
end.

(** Lists represented functions *)
Fixpoint list_functions (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (last_id : nat) 
      : list (nat * FunctionIdentifier * FunctionExpression) :=
match vl, paramss, bodies with
| [], [], [] => []
| v::vs, varl::ps, e::bs => insert_function last_id v varl e 
                                 (list_functions vs ps bs (S last_id))
| _, _, _ => []
end.

(** Add functions *)
Fixpoint append_funs_to_env_base (vl : list FunctionIdentifier) (paramss : list (list Var)) 
      (bodies : list Expression) (d : Environment) (def : Environment) 
      (deffuns : list (nat * FunctionIdentifier * FunctionExpression)) (last_id : nat) 
      : Environment :=
match vl, paramss, bodies with
| [], [], [] => d
| v::vs, varl::ps, e::bs => append_funs_to_env_base vs ps bs 
                              (insert_value d (inr v) 
                                           (VClos def deffuns last_id varl e)) 
                                           def deffuns (S last_id)
| _, _, _ => []
end.

Definition append_funs_to_env (l : list (FunctionIdentifier * ((list Var) * Expression))) (d : Environment) (last_id : nat) : Environment :=
append_funs_to_env_base (fst (split l)) (fst (split (snd (split l)))) (snd (split (snd (split l)))) d d 
                       (list_functions (fst (split l)) (fst (split (snd (split l)))) (snd (split (snd (split l)))) last_id)
                       last_id
.

Compute append_funs_to_env [(("f1"%string,0), ([], ErrorExp)) ; 
                            (("f2"%string,0), ([], ErrorExp)) ;
                            (("f1"%string,0), ([], ErrorExp)) ]
                           [(inl "X"%string, ErrorValue)] 0.

Compute insert_function 2 ("f1"%string, 0) [] ErrorExp (list_functions
                              [("f1"%string,0); ("f2"%string,0); ("f1"%string, 0)]
                              [[];[];[]]
                              [ErrorExp; ErrorExp; ErrorExp] 0).

(** Environment construction from the extension and the reference *)
Fixpoint get_env_base (env def : Environment) 
   (ext defext : list (nat * FunctionIdentifier * FunctionExpression))
   : Environment :=
match ext with
| [] => env
| (id, f1, (pl, b))::xs => get_env_base (insert_value env (inr f1) (VClos def defext id pl b)) def xs defext
end.

Definition get_env (env : Environment) 
   (ext : list (nat * FunctionIdentifier * FunctionExpression))
   : Environment :=
  get_env_base env env ext ext
.

Inductive SideEffectId : Set :=
| Input
| Output
.

Definition SideEffectList : Type := list (SideEffectId * list Value).

Definition nth_def {A : Type} (l : list A) (def err : A) (i : nat) :=
match i with
| 0 => def
| S i' => nth i' l err
end.

Lemma nth_def_eq {A : Type} (l : list A) (i : nat) (e1 def err : A):
  nth_def (e1::l) def err (S i) = nth_def l e1 err i.
Proof.
  simpl. destruct i.
  * simpl. reflexivity.
  * simpl. reflexivity.
Qed.

Theorem last_nth_equal {A : Type} (l : list A) (def err : A) :
  last l def = nth_def l def err (length l).
Proof.
  induction l.
  * auto.
  * simpl. rewrite IHl. destruct l.
    - auto.
    - simpl. auto.
Qed.

Proposition get_value_here (env : Environment) (var : Var + FunctionIdentifier) (val : Value):
get_value (insert_value env var val) var = inl val.
Proof.
  induction env.
  * simpl. rewrite uequal_refl. reflexivity.
  * simpl. destruct a. case_eq (var_funid_eqb s var); intro.
    - simpl. rewrite uequal_refl. reflexivity.
    - simpl. rewrite uequal_sym, H. assumption.
Qed.

(** Previous append result *)
Proposition get_value_there (env : Environment) (var var' : Var + FunctionIdentifier) 
     (val : Value):
var <> var' ->
get_value (insert_value env var val) var' = get_value env var'.
Proof.
  intro. induction env.
  * simpl. apply uequal_neq in H. rewrite uequal_sym in H. rewrite H. reflexivity.
  * simpl. destruct a. case_eq (var_funid_eqb s var); intro.
    - apply uequal_eq in H0. assert (var <> var'). auto. rewrite <- H0 in H.
      apply uequal_neq in H. rewrite uequal_sym in H. rewrite H. simpl. apply uequal_neq in H1.
      rewrite uequal_sym in H1. rewrite H1. reflexivity.
    - simpl. case_eq (var_funid_eqb var' s); intros.
      + reflexivity.
      + apply IHenv.
Qed.
