Require Export CE_Aux.

Import ListNotations.

Definition set_second {A B C : Type} (p : A * B * C) (b : B) : A * B * C :=
match p with
| (a, b0, c) => (a, b, c)
end.

Fixpoint eval_fbos_expr (env : Environment) (id : nat) (exp : Expression) (eff : SideEffectList) :
  nat * (Value + Exception) * SideEffectList :=
match exp with
 | ENil => (id, inl VNil, eff)
 | ELit l => (id, inl (VLit l), eff)
 | EVar v => (id, get_value env (inl v), eff)
 | EFunId f => (id, get_value env (inr f), eff)
 | EFun vl e => (S id, inl (VClos env [] id vl e), eff)
 | ECons hd tl =>
   match eval_fbos_expr env id hd eff with
   | (id', inl hdv, eff') =>
     match eval_fbos_expr env id' tl eff' with
     | (id'', inl tlv, eff'') => (id'', inl (VCons hdv tlv), eff'')
     | (id'', inr ex , eff'') => (id'', inr ex, eff'')
     end
   | (id', inr ex , eff') => (id', inr ex, eff')
   end
 | ETuple l => let res := 
           (fix eval_list env id exps eff : nat * ((list Value) + Exception) * SideEffectList := 
               match exps with
               | []    => (id, inl [], eff)
               | x::xs => match eval_fbos_expr env id x eff with
                          | (id', inl v , eff') => 
                            let res := eval_list env id' xs eff' in
                              match res with
                              | (id'', inl xs', eff'') => (id'', inl (v::xs'), eff'')
                              | (id'', inr ex , eff'') => (id'', inr ex, eff'')
                              end
                          | (id', inr ex, eff') => (id', inr ex, eff')
                          end
               end
               ) env id l eff
       in
       match res with
       | (id', inl vl, eff') => (id', inl (VTuple vl), eff')
       | (id', inr ex, eff') => (id', inr ex, eff')
       end
 | ECall f l => let res := 
           (fix eval_list env id exps eff : nat * ((list Value) + Exception) * SideEffectList := 
               match exps with
               | []    => (id, inl [], eff)
               | x::xs => match eval_fbos_expr env id x eff with
                          | (id', inl v , eff') => 
                            let res := eval_list env id' xs eff' in
                              match res with
                              | (id'', inl xs', eff'') => (id'', inl (v::xs'), eff'')
                              | (id'', inr ex , eff'') => (id'', inr ex, eff'')
                              end
                          | (id', inr ex, eff') => (id', inr ex, eff')
                          end
               end
               ) env id l eff
       in
       match res with
       | (id', inl vl, eff') => let (a, b) := eval f vl eff' in (id', a, b)
       | (id', inr ex, eff') => (id', inr ex, eff')
       end
 | EApp exp l =>
    match eval_fbos_expr env id exp eff with
    | (id', inr ex, eff') => (id', inr ex, eff')
    | (id', inl v , eff') => let res :=
      (fix eval_list env id exps eff : nat * ((list Value) + Exception) * SideEffectList := 
               match exps with
               | []    => (id, inl [], eff)
               | x::xs => match eval_fbos_expr env id x eff with
                          | (id', inl v , eff') => 
                            let res := eval_list env id' xs eff' in
                              match res with
                              | (id'', inl xs', eff'') => (id'', inl (v::xs'), eff'')
                              | (id'', inr ex , eff'') => (id'', inr ex, eff'')
                              end
                          | (id', inr ex, eff') => (id', inr ex, eff')
                          end
               end
               ) env id' l eff'
       in
       match res with
       | (id'', inl vl, eff'') =>
         match v with
         | VClos ref ext idcl varl body => if Nat.eqb (length vl) (length varl)
                                            then (id'', inl v, eff'')
                                            (* eval_fbos_expr (append_vars_to_env varl vl (get_env ref ext)) id'' body eff'' *)
                                            else (id'', inr (badarity v), eff'')
         | _                             => (id'', inr (badfun v), eff'')
         end
       | (id'', inr ex, eff'') => (id'', inr ex, eff'')
       end
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
 | ECase e l => (0, inr novar, [])
 | ELet var e1 e2 => 
    match eval_fbos_expr env id e1 eff with
    | (id', inr ex, eff') => (id', inr ex, eff')
    | (id', inl v , eff') => eval_fbos_expr (append_vars_to_env [var] [v] env) id' e2 eff'
    end
 | ELetRec f l b e => eval_fbos_expr (append_funs_to_env [(f, (l, b))] env id) (S id) e eff
 | ETry e1 v1 e2 vl2 e3 =>
    match eval_fbos_expr env id e1 eff with
    | (id', inr ex, eff') => eval_fbos_expr (append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env) id' e3 eff'
    | (id', inl v , eff') => eval_fbos_expr (append_vars_to_env [v1] [v] env) id' e2 eff'
    end
end
.

Example exp1 := ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) ( ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "Y"%string (ELit (Integer 5)) (EVar "Y"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ELet "X"%string (ELet "X"%string (ELit (Integer 5)) (EVar "X"%string)) (ECall "+"%string [EVar "X"%string; EVar "X"%string])))))))))))))))))))))))))))))))))))).

Compute eval_fbos_expr [] 0 exp1 [].