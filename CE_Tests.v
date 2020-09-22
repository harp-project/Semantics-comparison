Require Import CE_NOS.
Require Import CE_FBOS.
Require Import CE_PBOS.

Import ListNotations.

Open Scope string_scope.


(* Pretty big-step example evaluation *)
Goal
  | [], 0, ELet "X" (EFun ["Y"; "Z"] (EVar "Y")) (EApp (EVar "X") [ELit (Atom "a"); ELit (Atom "b")]), []|
-p>
  | 1, inl (VLit (Atom "a")), []|
.
Proof.
  eapply peval_let.
  * eapply peval_fun.
  * simpl.
    apply peval_let_fin. eapply peval_app.
    - eapply peval_var. reflexivity.
    - simpl. eapply peval_app1_fin.
      + eapply peval_list.
        ** apply peval_lit.
        ** eapply peval_list.
          -- apply peval_lit.
          -- apply peval_empty.
      + apply peval_app2_fin.
              *** reflexivity.
              *** apply peval_var. reflexivity.
Qed.

(* big-step example evaluation *)
Goal
  | [], 0, ELet "X" (EFun ["Y"; "Z"] (EVar "Y")) (EApp (EVar "X") [ELit (Atom "a"); ELit (Atom "b")]), []|
-e>
  | 1, inl (VLit (Atom "a")), []|
.
Proof.
  eapply eval_let.
  * eapply eval_fun.
  * eapply eval_app with (vals := [VLit (Atom "a"); VLit (Atom "b")])
                         (eff := [[];[]])
                         (ids := [1; 1]).
    - reflexivity.
    - apply eval_var. reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros. inversion H. 2: inversion H1. 3: inversion H3.
      + apply eval_lit.
      + apply eval_lit.
    - apply eval_var. reflexivity.
Qed.

(* functional big-step evaluation *)
Compute eval_fbos_expr [] 0 (ELet "X" (EFun ["Y"; "Z"] (EVar "Y")) (EApp (EVar "X") [ELit (Atom "a"); ELit (Atom "b")])) [] 1000.

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

Import List.

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