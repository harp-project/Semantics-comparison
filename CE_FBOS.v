Require Export CE_Aux.

Import ListNotations.

Import Lia.

Definition set_second {A B C : Type} (p : A * B * C) (b : B) : A * B * C :=
match p with
| (a, b0, c) => (a, b, c)
end.

(* I can't import stdlib implementation somehow *)
Definition list_sum l := fold_right plus 0 l.

Fixpoint exp_size (e : Expression) : nat :=
match e with
 | ENil => 1
 | ELit l => 1
 | EVar v => 1
 | EFunId f => 1
 | EFun vl e => 1
 | ECons hd tl => 1 + exp_size hd + exp_size tl
 | ETuple l => 1 + list_sum (map exp_size l)
 | ECall f l => 1 + list_sum (map exp_size l)
 | EApp exp l => 1 + list_sum (map exp_size l) + exp_size exp
 | ECase e l => 1 + exp_size e + fold_right (fun '(a, b, c) r => r + exp_size b + exp_size c) 0 l
 | ELet v e1 e2 => 1 + exp_size e1 + exp_size e2
 | ELetRec f l b e => 1 + exp_size e
 | ETry e1 v1 e2 vl2 e3 => 1 + exp_size e1 + exp_size e2 + exp_size e3
end.

Fixpoint eval_list (f: Environment -> nat -> Expression -> SideEffectList -> nat -> option (nat * (Value + Exception) * SideEffectList)) (env : Environment) (id : nat) (exps : list Expression) (eff : SideEffectList) (clock : nat) : option (nat * ((list Value) + Exception) * SideEffectList) := 
 match exps with
 | []    => Some (id, inl [], eff)
 | x::xs => match f env id x eff clock with
            | Some (id', inl v , eff') => 
              let res := eval_list f env id' xs eff' clock in
                match res with
                | Some (id'', inl xs', eff'') => Some (id'', inl (v::xs'), eff'')
                | r => r
                end
            | Some (id', inr ex, eff') => Some (id', inr ex, eff')
            | None => None
            end
 end
 .

Fixpoint list_eqb {A : Type} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| x::xs, y::ys => eq x y && list_eqb eq xs ys
| _, _ => false
end.

Definition effect_id_eqb (id1 id2 : SideEffectId) : bool :=
match id1, id2 with
 | Input, Input => true
 | Output, Output => true
 | _, _ => false
end.


Definition effect_eqb (e1 e2 : SideEffectId * list Value) : bool :=
match e1, e2 with
| (id1, vals1), (id2, vals2) => effect_id_eqb id1 id2 && list_eqb Value_eqb vals1 vals2
end.

Inductive ResultType : Type :=
| Result (id : nat) (res : Value + Exception) (eff : SideEffectList)
| Timeout
| Failure.

Inductive ResultListType : Type :=
| LResult (id : nat) (res : list Value + Exception) (eff : SideEffectList)
| LTimeout
| LFailure.


Fixpoint eval_fbos_expr (env : Environment) (id : nat) (exp : Expression) (eff : SideEffectList)  (clock : nat) : 
  ResultType :=
match clock with
| 0 => Timeout
| S clock' =>
   match exp with
   | ENil => Result id (inl VNil) eff
   | ELit l => Result id (inl (VLit l)) eff
   | EVar v => Result id (get_value env (inl v)) eff
   | EFunId f => Result id (get_value env (inr f)) eff
   | EFun vl e => Result (S id) (inl (VClos env [] id vl e)) eff
   | ECons hd tl =>
     match eval_fbos_expr env id tl eff clock' with
     | Result id' (inl tlv) eff' =>
       match eval_fbos_expr env id' hd eff' clock' with
       | Result id'' (inl hdv) eff'' => Result id'' (inl (VCons hdv tlv)) eff''
       | r => r
       end
     | r => r
     end
   | ETuple l => 
   let res := 
      (fix eval_list env id exps eff : ResultListType := 
                 match exps with
                 | []    => LResult id (inl []) eff
                 | x::xs => 
                    match eval_fbos_expr env id x eff clock' with
                    | Result id' (inl v) eff' => 
                      let res := eval_list env id' xs eff' in
                        match res with
                        | LResult id'' (inl xs') eff'' => LResult id'' (inl (v::xs')) eff''
                        | r => r
                        end
                    | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
                    | Failure => LFailure
                    | Timeout => LTimeout
                    end
                 end
                 ) env id l eff
         in
         match res with
         | LResult id' (inl vl) eff' => Result id' (inl (VTuple vl)) eff'
         | LResult id' (inr ex) eff' => Result id' (inr ex) eff'
         | LFailure => Failure
         | LTimeout => Timeout
         end
   | ECall f l => let res := 
             (fix eval_list env id exps eff : ResultListType := 
                 match exps with
                 | []    => LResult id (inl []) eff
                 | x::xs => 
                    match eval_fbos_expr env id x eff clock' with
                    | Result id' (inl v) eff' => 
                      let res := eval_list env id' xs eff' in
                        match res with
                        | LResult id'' (inl xs') eff'' => LResult id'' (inl (v::xs')) eff''
                        | r => r
                        end
                    | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
                    | Failure => LFailure
                    | Timeout => LTimeout
                    end
                 end
                 ) env id l eff
         in
         match res with
         | LResult id' (inl vl) eff' => let (a, b) := eval f vl eff' in Result id' a b
         | LResult id' (inr ex) eff' => Result id' (inr ex) eff'
         | LFailure => Failure
         | LTimeout => Timeout
         end
   | EApp exp l =>
      match eval_fbos_expr env id exp eff clock' with
      | Result id' (inl v) eff' => let res :=
        (fix eval_list env id exps eff : ResultListType := 
                 match exps with
                 | []    => LResult id (inl []) eff
                 | x::xs => 
                    match eval_fbos_expr env id x eff clock' with
                    | Result id' (inl v) eff' => 
                      let res := eval_list env id' xs eff' in
                        match res with
                        | LResult id'' (inl xs') eff'' => LResult id'' (inl (v::xs')) eff''
                        | r => r
                        end
                    | Result id' (inr ex) eff' => LResult id' (inr ex) eff'
                    | Failure => LFailure
                    | Timeout => LTimeout
                    end
                 end
                 ) env id l eff
         in
         match res with
         | LResult id'' (inl vl) eff'' =>
           match v with
           | VClos ref ext idcl varl body => if Nat.eqb (length vl) (length varl)
                                             then
                                               eval_fbos_expr (append_vars_to_env varl vl (get_env ref ext)) id'' body eff'' (clock')
                                             else Result id'' (inr (badarity v)) eff''
           | _                             => Result id'' (inr (badfun v)) eff''
           end
         | LResult id'' (inr ex) eff'' => Result id'' (inr ex) eff''
         | LFailure => Failure
         | LTimeout => Timeout
         end
       | r => r
   end
  | ECase e l =>
      match eval_fbos_expr env id e eff clock' with
      | Result id' (inl v) eff' =>
       (fix clause_eval l i' :=
       let i := (length l) - i' in
         match i' with
         | 0 => Result id' (inr if_clause) eff'
         | S i'' =>
           match match_clause v l i with
           | Some (gg, bb, bindings) =>
             match eval_fbos_expr (add_bindings bindings env) id' gg eff' clock' with
             | Result id'' (inl v) eff'' =>  
                match v with
                | VLit (Atom "true"%string)  => 
                    if andb (Nat.eqb id'' id') (list_eqb effect_eqb eff' eff'')
                    then eval_fbos_expr (add_bindings bindings env) id' bb eff' clock'
                    else Failure (* guards cannot produce side effects *)
                | VLit (Atom "false"%string) => clause_eval l i''
                | _ => Failure
                end
             | Timeout => Timeout
             | _ => Failure (* exception is a side effect, so it can't happen in guards *)
             end
           | None              => clause_eval l i''
           end
         end
       ) l (length l)
     | r => r
     end
   | ELet var e1 e2 => 
      match eval_fbos_expr env id e1 eff clock' with
      | Result id' (inl v) eff' => eval_fbos_expr (append_vars_to_env [var] [v] env) id' e2 eff' clock'
      | r => r
      end
   | ELetRec f l b e => eval_fbos_expr (append_funs_to_env [(f, (l, b))] env id) (S id) e eff clock'
   | ETry e1 v1 e2 vl2 e3 =>
      match eval_fbos_expr env id e1 eff clock' with
      | Result id' (inr ex) eff' => eval_fbos_expr (append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env) id' e3 eff' clock'
      | Result id' (inl v) eff' => eval_fbos_expr (append_vars_to_env [v1] [v] env) id' e2 eff' clock'
      | r => r
      end
  end
end
.

Example exp1 := ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "Y"%string (ELit (Integer 5)) (EVar "Y"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ECall "+"%string [EVar "X"%string; EVar "X"%string])))))))))))))))))))))))))))))))))))).

Compute eval_fbos_expr [] 0 exp1 [] 10000.

Import StringSyntax.

Lemma nil_length {A}: @length A [] = 0.
Proof. auto. Qed.
