Require Export CE_Syntax.
Require Lia.
From Coq Require Classes.EquivDec.
From Coq Require Lists.ListSet.

Export Lists.List.
Export Arith.PeanoNat.
Import Classes.EquivDec.
Export Lia.

Import ListNotations.
Import Lists.ListSet.

Section list_proofs.

Lemma list_length_helper_refl {A : Type} : forall l : list A, length l =? length l = true.
Proof.
  induction l.
  * auto.
  * auto.
Qed.

Lemma list_length_helper {A : Type} : forall l l' : list A, length l = length l' -> length l =? length l' = true.
Proof.
  intros. induction l.
  * inversion H. auto.
  * inversion H. simpl. apply list_length_helper_refl.
Qed.

(** If the list is longer than 0, then it has a first element *)
Lemma element_exist {A : Type} : forall n (l : list A), S n = length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.

Proposition list_length {A : Type} {a : A} {l : list A} : length (a :: l) > 0.
Proof.
  simpl. apply Nat.lt_0_succ.
Qed.

Theorem last_element_equal {A : Type} (l : list A) (def def2 : A):
  last l def = last (def :: l) def2.
Proof.
  induction l.
  * auto.
  * simpl. rewrite IHl. simpl. destruct l; auto.
Qed.

End list_proofs.

Section Nat_Proofs.

Proposition nat_ge_or : forall {n m : nat}, n >= m <-> n = m \/ n > m.
Proof.
  intros. lia.
Qed.

Lemma nat_lt_zero (i j : nat):
  j < i -> exists j', i = S j'.
Proof.
  intros. destruct i.
  * inversion H.
  * exists i. reflexivity.
Qed.

End Nat_Proofs.

(** The matching function of two literals *)
Definition match_literals (l l' : Literal) : bool :=
match l, l' with
| Atom s, Atom s' => eqb s s'
| Integer x, Integer x' => Z.eqb x x'
| _, _ => false
end.

(** Pattern matching success checker *)
Fixpoint match_value_to_pattern (e : Value) (p : Pattern) : bool :=
match p with
| PNil => 
   match e with
   | VNil => true
   | _ => false
   end
| PVar v => true (* every e matches to a pattern variable *)
| PLit l => match e with
  | VLit l' => match_literals l l'
  | _ => false
  end
| PCons hd tl => match e with
  | VCons hd' tl' => (match_value_to_pattern hd' hd) && (match_value_to_pattern tl' tl)
  | _ => false
  end
| PTuple l => match e with
  | VTuple exps => (fix match_elements vl pl :=
                     match vl, pl with
                     | [], [] => true
                     | _, [] => false
                     | [], _ => false
                     | (v::vs), (p::ps) => andb (match_value_to_pattern v p) 
                                                (match_elements vs ps)
                     end) exps l
  | _ => false
  end
end
.

(** Examples *)
Compute match_value_to_pattern (VClos [] [] 0 [] (ErrorExp)) (PVar "X"%string).
Compute match_value_to_pattern (VLit (Atom "a"%string)) (PVar "X"%string).
Compute match_value_to_pattern (VLit (Atom "a"%string)) (PLit (Atom "a"%string)).
Compute match_value_to_pattern (VLit (Atom "a"%string)) (PEmptyTuple).
Compute match_value_to_pattern (VTuple [VLit (Atom "a"%string) ; VLit (Integer 1)]) 
                               (PVar "X"%string).
Compute match_value_to_pattern (VTuple [VLit (Atom "a"%string) ; VLit (Integer 1)]) 
                               (PTuple [PVar "X"%string ; PLit (Integer 1)]).

(** Used variables in a pattern *)
Fixpoint variable_occurances (p : Pattern) : list Var :=
match p with
 | PNil => []
 | PVar v => [v]
 | PLit l => []
 | PCons hd tl => variable_occurances hd ++ variable_occurances tl
 | PTuple l => (fix variable_occurances_list l :=
                   match l with
                   | [] => []
                   | pat::ps => variable_occurances pat ++ variable_occurances_list ps
                   end) l
end.

(** Used variables in a pattern, but now with sets *)
Fixpoint variable_occurances_set (p : Pattern) : set Var :=
match p with
 | PNil => []
 | PVar v => [v]
 | PLit l => []
 | PCons hd tl => set_union string_dec (variable_occurances_set hd) (variable_occurances_set tl)
 | PTuple l => (fix variable_occurances_set_list t :=
                    match t with
                    | [] => []
                    | pat::ps => set_union string_dec (variable_occurances_set pat) 
                                                      (variable_occurances_set_list ps)
                    end) l
end.



(** Extended matching function, results the variable binding list 
    Should be used together with match_value_to_pattern *)
Fixpoint match_value_bind_pattern (e : Value) (p : Pattern) : list (Var * Value) :=
match p with
| PNil => match e with
                | VNil => []
                | _ => [] (** error *)
                end
| PVar v => [(v, e)] (** every e matches to a pattern variable *)
| PLit l => match e with
  | VLit l' => if match_literals l l' then [] else [] (* Error *)
  | _ => [] (** error *)
  end
| PCons hd tl => match e with
  | VCons hd' tl' => (match_value_bind_pattern hd' hd) ++ (match_value_bind_pattern tl' tl)
  | _ => [] (** error *)
  end
| PTuple pl => match e with
  | VTuple exps => (fix match_and_bind_elements exps t :=
                        match exps with
                        | [] => match t with
                          | [] => []
                          | _ => [] (** error *)
                          end
                        | e::es => match t with
                          | p::ps => (match_value_bind_pattern e p) ++ 
                                     (match_and_bind_elements es ps) 
(** Each variable can occur only once in a pattern according to the Core-Erlang documentation *)
                          |_ => [] (** error *)
                          end 
                        end) exps pl
  | _ => []
  end
end
.

(** Examples *)
Compute match_value_bind_pattern (VClos [] [] 0 [] (ErrorExp)) (PVar "X"%string).
Compute match_value_bind_pattern (VLit (Atom "a"%string)) (PVar "X"%string).
Compute match_value_bind_pattern (VLit (Atom "a"%string)) (PLit (Atom "alma"%string)).
Compute match_value_bind_pattern (VLit (Atom "a"%string)) (PEmptyTuple).
Compute match_value_bind_pattern (VTuple [VLit (Atom "a"%string) ; VLit (Integer 1)]) 
                                 (PVar "X"%string).
Compute match_value_to_pattern (VTuple [VLit (Atom "a"%string) ; 
                                        VLit (Integer 1); VLit (Integer 2)]) 
                               (PTuple [PVar "X"%string ; PVar "Y"%string]).
Compute match_value_bind_pattern (VTuple [VLit (Atom "a"%string) ; VLit (Integer 1); 
                                          VLit (Integer 2)]) 
                                 (PTuple [PVar "X"%string ; PVar "Y"%string]).

(** From the list of patterns, guards and bodies, this function decides if a value matches the ith clause *)
Fixpoint match_clause (e : Value) (l : list (Pattern * Expression * Expression)) (i : nat) : option (Expression * Expression * list (Var * Value)) :=
match l, i with
| [], _ => None
| (p,g,exp)::xs, 0 => if match_value_to_pattern e p then Some (g, exp, (match_value_bind_pattern e p)) else None
| (p, g, e0)::xs, S n' => match_clause e xs n'
end
.

(* (** TODO: Clause checker *)
Fixpoint correct_clauses (ps : list (list Pattern)) (gs : list Expression) (bs : list Expression) : bool :=
match ps, gs, bs with
| [], [], [] => true
| p::ps, g::gs, exp::es => 
   ((length (fold_right variable_occurances [] p)) =? (length (variable_occurances_set p))) && 
   correct_clauses ps gs es
| _, _, _ => false
end. *)

(* Examples *)
Compute variable_occurances (PTuple [PVar "X"%string ; PVar "X"%string]).
Compute variable_occurances_set (PTuple [PVar "X"%string ; PVar "X"%string]).

(** Get the used variables of an expression *)
Fixpoint variables (e : Expression) : list Var :=
match e with
  | ENil => []
  | ELit l => []
  | EVar v => [v]
  | EFunId f => []
  | EFun vl e => variables e
  | ECons hd tl => app (variables hd) (variables tl)
  | ETuple l => flat_map variables l
  | ECall f l => flat_map variables l
  | EApp exp l => app (variables exp) (flat_map variables l)
  | ECase e l => variables e ++ fold_right (fun '(a, b, c) r => app (app (variables b) (variables c)) r) [] l
  | ELet v e1 e2 => [v] ++ (variables e1) ++ (variables e2)
  | ELetRec f l b e => variables e
  | ETry e1 v1 e2 vl2 e3 => [v1] ++ vl2 ++ variables e1 ++ variables e2 ++ variables e3
end.

Definition funid_eqb (v1 v2 : FunctionIdentifier) : bool :=
match v1, v2 with
| (fid1, num1), (fid2, num2) => eqb fid1 fid2 && Nat.eqb num1 num2
end.

(* Extended equality between functions and vars *)
Definition var_funid_eqb (v1 v2 : Var + FunctionIdentifier) : bool :=
match v1, v2 with
| inl s1, inl s2 => eqb s1 s2
| inr f1, inr f2 => funid_eqb f1 f2
| _, _ => false
end.
