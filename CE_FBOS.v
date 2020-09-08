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




Fixpoint eval_fbos_expr (env : Environment) (id : nat) (exp : Expression) (eff : SideEffectList)  (clock : nat) : 
  option (nat * (Value + Exception) * SideEffectList) :=
match clock with
| 0 => None
| S clock' =>
   match exp with
   | ENil => Some (id, inl VNil, eff)
   | ELit l => Some (id, inl (VLit l), eff)
   | EVar v => Some (id, get_value env (inl v), eff)
   | EFunId f => Some (id, get_value env (inr f), eff)
   | EFun vl e => Some (S id, inl (VClos env [] id vl e), eff)
   | ECons hd tl =>
     match eval_fbos_expr env id hd eff clock' with
     | Some (id', inl hdv, eff') =>
       match eval_fbos_expr env id' tl eff' clock' with
       | Some (id'', inl tlv, eff'') => Some (id'', inl (VCons hdv tlv), eff'')
       | r => r
       end
     | r => r
     end
   | ETuple l => 
   let res := 
      (fix eval_list env id exps eff : option (nat * ((list Value) + Exception) * SideEffectList) := 
                 match exps with
                 | []    => Some (id, inl [], eff)
                 | x::xs => match eval_fbos_expr env id x eff clock' with
                            | Some (id', inl v , eff') => 
                              let res := eval_list env id' xs eff' in
                                match res with
                                | Some (id'', inl xs', eff'') => Some (id'', inl (v::xs'), eff'')
                                | r => r
                                end
                            | Some (id', inr ex, eff') => Some (id', inr ex, eff')
                            | None => None
                            end
                 end
                 ) env id l eff
         in
         match res with
         | Some (id', inl vl, eff') => Some (id', inl (VTuple vl), eff')
         | Some (id', inr ex, eff') => Some (id', inr ex, eff')
         | None => None
         end
   | ECall f l => let res := 
             (fix eval_list env id exps eff : option (nat * ((list Value) + Exception) * SideEffectList) := 
                 match exps with
                 | []    => Some (id, inl [], eff)
                 | x::xs => match eval_fbos_expr env id x eff clock' with
                            | Some (id', inl v , eff') => 
                              let res := eval_list env id' xs eff' in
                                match res with
                                | Some (id'', inl xs', eff'') => Some (id'', inl (v::xs'), eff'')
                                | r => r
                                end
                            | Some (id', inr ex, eff') => Some (id', inr ex, eff')
                            | None => None
                            end
                 end
                 ) env id l eff
         in
         match res with
         | Some (id', inl vl, eff') => let (a, b) := eval f vl eff' in Some (id', a, b)
         | Some (id', inr ex, eff') => Some (id', inr ex, eff')
         | None => None
         end
   | EApp exp l =>
      match eval_fbos_expr env id exp eff clock' with
      | Some (id', inl v , eff') => let res :=
        (fix eval_list env id exps eff : option (nat * ((list Value) + Exception) * SideEffectList) := 
                 match exps with
                 | []    => Some (id, inl [], eff)
                 | x::xs => match eval_fbos_expr env id x eff clock' with
                            | Some (id', inl v , eff') => 
                              let res := eval_list env id' xs eff' in
                                match res with
                                | Some (id'', inl xs', eff'') => Some (id'', inl (v::xs'), eff'')
                                | r => r
                                end
                            | Some (id', inr ex, eff') => Some (id', inr ex, eff')
                            | None => None
                            end
                 end
                 ) env id l eff
         in
         match res with
         | Some (id'', inl vl, eff'') =>
           match v with
           | VClos ref ext idcl varl body => if Nat.eqb (length vl) (length varl)
                                              then (* Some (id'', inl v, eff'') *)
                                              eval_fbos_expr (append_vars_to_env varl vl (get_env ref ext)) id'' body eff'' (clock')
                                              else Some (id'', inr (badarity v), eff'')
           | _                             => Some (id'', inr (badfun v), eff'')
           end
         | Some (id'', inr ex, eff'') => Some (id'', inr ex, eff'')
         | None => None
         end
   | r => r
   end
  (*  | ECase e l =>
      match eval_fbos_expr env id e eff with
      | (id', inr ex, eff') => (id', inr ex, eff')
      | (id', inl v , eff') =>
       (fix clause_eval l i' :=
       let i := (length l) - i' in
         match i' with
         | 0 => (id', inr if_clause, eff')
         | S i'' =>
         (* TODO: side effects cannot be produced here *)
           match match_clause v l i with
           | Some (gg, bb, bindings) =>
             match eval_fbos_expr (add_bindings bindings env) id' gg eff' with
             | (id'', inl v, eff'') =>  match v with
                                        | VLit (Atom "true"%string)  => 
                                            if (Nat.eqb id'' id') (* TODO: SE lists equal *)
                                            then eval_fbos_expr (add_bindings bindings env) id' bb eff'
                                            else (* undef *) (id'', inr novar, eff'')
                                        | VLit (Atom "false"%string) => clause_eval l i''
                                        | _ => (* TODO: undef *) (id', inr novar, eff')
                                        end
             | _                         => (* TODO: undef *) (id', inr novar, eff')
             end
           | None              => clause_eval l i''
           end
         end
       ) l (length l)
    end *)
   | ECase e l => Some (0, inr novar, [])
   | ELet var e1 e2 => 
      match eval_fbos_expr env id e1 eff clock' with
      | Some (id', inl v , eff') => eval_fbos_expr (append_vars_to_env [var] [v] env) id' e2 eff' clock'
      | r => r
      end
   | ELetRec f l b e => eval_fbos_expr (append_funs_to_env [(f, (l, b))] env id) (S id) e eff clock'
   | ETry e1 v1 e2 vl2 e3 =>
      match eval_fbos_expr env id e1 eff clock' with
      | Some (id', inr ex, eff') => eval_fbos_expr (append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env) id' e3 eff' clock'
      | Some (id', inl v , eff') => eval_fbos_expr (append_vars_to_env [v1] [v] env) id' e2 eff' clock'
      | None => None
      end
  end
end
.

Example exp1 := ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "Y"%string (ELit (Integer 5)) (EVar "Y"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ECall "+"%string [EVar "X"%string; EVar "X"%string])))))))))))))))))))))))))))))))))))).

Compute eval_fbos_expr [] 0 exp1 [] 10000.