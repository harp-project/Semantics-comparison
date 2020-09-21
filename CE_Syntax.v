From Coq Require ZArith.BinInt.
From Coq Require Strings.String.
From Coq Require Structures.OrderedTypeEx.

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.

Import ListNotations.

Definition Var : Type := string.

Inductive Literal : Type :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).


Inductive Pattern : Type :=
| PVar     (v : Var)
| PLit (l : Literal)
(* | PCons  (hd tl : Pattern)
| PTuple (l : list Pattern) *)
| PNil.

(* Definition PEmptyTuple : Pattern := PTuple []. *)

Definition FunctionIdentifier : Type := string * nat.

Inductive Expression : Type :=
| ENil
| ELit    (l : Literal)
| EVar    (v : Var)
| EFunId  (f : FunctionIdentifier)
| EFun    (vl : list Var) (e : Expression)
(* | ECons   (hd tl : Expression) *)
(* | ETuple  (l : list Expression) *)
| ECall   (f : string) (l : list Expression)
(** For function applications: *)
| EApp    (exp: Expression)     (l : list Expression)
(* | ECase   (e : Expression) (l : list (Pattern * Expression * Expression)) *)
| ELet    (v : Var) (e1 e2 : Expression)
| ELetRec (f : FunctionIdentifier) (l : list Var) (b : Expression) (e : Expression)
| ETry    (e1 : Expression) (v1 : Var) (e2 : Expression) (vl2 : list Var) (e2 : Expression).

Definition FunctionExpression : Type := list Var * Expression.

(** What expressions are in normal form 
    According to CE lang spec. value sequences cannot be nested
*)
Inductive Value : Type :=
| VNil
| VLit     (l : Literal)
| VClos    (env : list ((Var + FunctionIdentifier) * Value))
           (ext : list (nat * FunctionIdentifier * FunctionExpression))
           (id : nat)
           (vl : list Var)
           (e : Expression)
(* | VCons    (vhd vtl : Value)
| VTuple   (vl : list Value) *).

(** Helper definitions *)
(* Definition VEmptyTuple : Value := VTuple []. *)

Definition ErrorValue : Value := (VLit (Atom "error"%string)).
Definition ErrorExp : Expression := (ELit (Atom "error"%string)).
Definition ErrorPat : Pattern := PLit(Atom "error"%string).
Definition ttrue : Value := VLit (Atom "true").
Definition ffalse : Value := VLit (Atom "false").
Definition ok : Value := VLit (Atom "ok").

(** Exception representation *)
Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Definition exclass_to_value (ex : ExceptionClass) : Value :=
match ex with
| Error => VLit (Atom "error"%string)
| Throw => VLit (Atom "throw"%string)
| Exit => VLit (Atom "exit"%string)
end.


(** Exception class, 1st Value : cause, 2nd Value : further details *)
Definition Exception : Type := ExceptionClass * Value * Value.

Definition badarith (v : Value) : Exception :=
  (Error, VLit (Atom "badarith"%string), v).
Definition badarg (v : Value) : Exception :=
  (Error, VLit (Atom "badarg"%string), v).
Definition novar : Exception := (Throw, VLit (Atom "novar"%string), ErrorValue).
Definition undef (v : Value) : Exception :=
  (Error, VLit (Atom "undef"%string), v).
Definition badfun (v : Value) : Exception := 
  (Error,VLit (Atom "badfun"%string), v).
Definition badarity (v : Value) : Exception := 
  (Error,VLit (Atom "badarity"%string), v).
Definition if_clause : Exception := 
  (Error, VLit (Atom "if_clause"%string), ErrorValue).

Definition Literal_eqb (l1 l2 : Literal) : bool :=
match l1, l2 with
| Atom s1, Atom s2 => eqb s1 s2
| Integer x1, Integer x2 => Z.eqb x1 x2
| _, _ => false
end.


Fixpoint Pattern_eqb (p1 p2 : Pattern) {struct p1} : bool :=
match p1, p2 with
| PVar v1, PVar v2 => eqb v1 v2
| PLit l1, PLit l2 => Literal_eqb l1 l2
(* | PCons hd tl, PCons hd' tl' => Pattern_eqb hd hd' && Pattern_eqb tl tl'
| PTuple l, PTuple l' => (fix blist_eq l l' := match l, l' with
                                     | [], [] => true
                                     | x::xs, x'::xs' => andb (Pattern_eqb x x') (blist_eq xs xs')
                                     | _, _ => false
                                     end) l l' *)
| PNil, PNil => true
| _, _ => false
end.

Fixpoint Value_eqb (e1 e2 : Value) : bool :=
match e1, e2 with
| VNil, VNil => true
| VLit l, VLit l' => Literal_eqb l l'
| VClos env ext id p b, VClos env' ext' id' p' b' => Nat.eqb id id'
(* | VCons hd tl, VCons hd' tl' => Value_eqb hd hd' && Value_eqb tl tl'
| VTuple l, VTuple l' => (fix blist l l' := match l, l' with
                                           | [], [] => true
                                           | x::xs, x'::xs' => andb (Value_eqb x x') (blist xs xs')
                                           | _, _ => false
                                           end) l l' *)
| _, _ => false
end.
