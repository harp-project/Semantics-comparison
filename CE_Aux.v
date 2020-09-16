Require Export CE_Env.

Import ListNotations.

(** For biuilt-in arithmetic calls *)
Definition eval_arith (fname : string) (params : list Value) :  Value + Exception :=
match fname, params with
(** addition *)
| "+"%string, [VLit (Integer a); VLit (Integer b)] => inl (VLit (Integer (a + b)))
| "+"%string, [a; b]                               => inr (badarith (VCons a b))
(** subtraction *)
| "-"%string, [VLit (Integer a); VLit (Integer b)] => inl (VLit (Integer (a - b)))
| "-"%string, [a; b]                               => inr (badarith (VCons a b))
(** unary minus *)
| "-"%string, [VLit (Integer a)]                   => inl (VLit (Integer (0 - a)))
| "-"%string, [a]                                  => inr (badarith a)
(** multiplication *)
| "*"%string, [VLit (Integer a); VLit (Integer b)] => inl (VLit (Integer (a * b)))
| "*"%string, [a; b]                               => inr (badarith (VCons a b))
(** division *)
| "/"%string, [VLit (Integer a); VLit (Integer b)] => inl (VLit (Integer (a / b)))
| "/"%string, [a; b]                               => inr (badarith (VCons a b))
(** rem *)
| "rem"%string, [VLit (Integer a); VLit (Integer b)] => inl (VLit (Integer (Z.rem a b)))
| "rem"%string, [a; b]                               => inr (badarith (VCons a b))
(** div *)
| "div"%string, [VLit (Integer a); VLit (Integer b)] => inl (VLit (Integer (Z.div a b)))
| "div"%string, [a; b]                               => inr (badarith (VCons a b))
(** anything else *)
| _         , _                                    => inr (undef (VLit (Atom fname)))
end.

(** For IO maniputaion: *)
Definition eval_io (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((Value + Exception) * SideEffectList) :=
match fname, length params, params with
(** writing *)
| "fwrite"%string, 1, _ => (inl ok                                    , eff ++ [(Output, params)] )
(** reading *)
| "fread"%string , 2, e => (inl (VTuple [ok; nth 1 params ErrorValue]), eff ++ [(Input,  params)])
(** anything else *)
| _              , _, _ => (inr (undef (VLit (Atom fname)))           , eff)
end.

Definition transform_tuple (v : Value) : Value + Exception :=
match v with
| VTuple l => inl ((fix unfold_list l :=
                   match l with
                   | [] => VNil
                   | x::xs => VCons x (unfold_list xs)
                   end) l)
| _        => inr (badarg v)
end.

Fixpoint transform_list (v : Value) : list Value + Exception :=
match v with
| VNil      => inl []
| VCons x y => match y with
               | VNil => inl [x]
               | VCons z w => match (transform_list y) with
                              | inr ex => inr ex
                              | inl res => inl (x::res)
                              end
               | z => inr (badarg v)
               end
| _         => inr (badarg v)
end.

Definition eval_list_tuple (fname : string) (params : list Value) : Value + Exception :=
match fname, params with
| "tuple_to_list"%string, [v] => transform_tuple v
| "list_to_tuple"%string, [v] => match (transform_list v) with
                                 | inr ex => inr ex
                                 | inl l => inl (VTuple l)
                                 end
| _                     , _   => inr (undef (VLit (Atom fname)))
end.

Definition eval_length (params : list Value) : Value + Exception :=
match params with
| [v] => let res :=
          (fix len val := match val with
                         | VNil => inl Z.zero
                         | VCons x y => let res := len y in
                                          match res with
                                          | inl n => inl (Z.add 1 n)
                                          | inr _ => res
                                          end
                         | _ => inr (badarg v)
                         end) v in
        match res with
        | inl n => inl (VLit (Integer n))
        | inr ex => inr ex
        end
| _ => inr (undef (VLit (Atom "length")))
end.

Definition eval_tuple_size (params : list Value) : Value + Exception :=
match params with
| [VTuple l] => inl (VLit (Integer (Z.of_nat (length l))))
| [v] => inr (badarg v)
| _ => inr (undef (VLit (Atom "tuple_size")))
end.

Definition eval_hd_tl (fname : string) (params : list Value) : Value + Exception :=
match fname, params with
| "hd"%string, [VCons x y] => inl x
| "hd"%string, [v] => inr (badarg v)
| "tl"%string, [VCons x y] => inl y
| "tl"%string, [v] => inr (badarg v)
| _, _ => inr (undef (VLit (Atom fname)))
end.

Fixpoint replace_nth_error {A : Type} (l : list A) (i : nat) (e : A) : option (list A) :=
match i, l with
| 0, x::xs => Some (e::xs)
| _, [] => None
| S n, x::xs => match (replace_nth_error xs n e) with
               | None => None
               | Some l' => Some (x::l')
               end
end.

Definition eval_elem_tuple (fname : string) (params : list Value) : Value + Exception :=
match fname, params with
| "element"%string, [VLit (Integer i); VTuple l] =>
    match i with
    | Z.pos p => match nth_error l (pred (Pos.to_nat p)) with
                 | None   => inr (badarg (VCons (VLit (Integer i)) (VTuple l)))
                 | Some v => inl v
                 end
    | _       => inr (badarg (VCons (VLit (Integer i)) (VTuple l)))
    end
| "element"%string, [v1; v2] => inr (badarg (VCons v1 v2))
| "setelement"%string, [VLit (Integer i); VTuple l; val] =>
    match i with
    | Z.pos p => match replace_nth_error l (pred (Pos.to_nat p)) val with
                 | None    => inr (badarg (VCons (VLit (Integer i)) (VCons (VTuple l) val)))
                 | Some l' => inl (VTuple l')
                 end
    | _       => inr (badarg (VCons (VLit (Integer i)) (VTuple l)))
    end
| "setelement"%string, [v1; v2; v3] => inr (badarg (VCons v1 (VCons v2 v3)))
| _, _ => inr (undef (VLit (Atom fname)))
end.

(* TODO: Always can be extended, this function simulates inter-module calls *)
Definition eval (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((Value + Exception) * SideEffectList) :=
match fname with
| "+"%string      | "-"%string
| "*"%string      | "/"%string
| "rem"%string    | "div"%string   => (eval_arith fname params, eff)
| "fwrite"%string | "fread"%string => eval_io fname params eff
| "tuple_to_list"%string
| "list_to_tuple"%string           => (eval_list_tuple fname params, eff)
| "length"%string                  => (eval_length params, eff)
| "tuple_size"%string              => (eval_tuple_size params, eff)
| "hd"%string     | "tl"%string    => (eval_hd_tl fname params, eff)
| "element"%string
| "setelement"%string              => (eval_elem_tuple fname params, eff)
(** anything else *)
| _                                => (inr (undef (VLit (Atom fname))), eff)
end.
