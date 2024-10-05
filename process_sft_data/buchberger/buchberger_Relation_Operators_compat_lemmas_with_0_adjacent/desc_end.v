Require Import List.
Require Import Relation_Operators.
Require Import Transitive_Closure.
Local Open Scope list_scope.
Section Lexicographic_Exponentiation.
Variable A : Set.
Variable leA : A -> A -> Prop.
Let Nil := nil (A:=A).
Let List := list A.
Inductive Ltl : List -> List -> Prop := | Lt_nil (a:A) (x:List) : Ltl Nil (a :: x) | Lt_hd (a b:A) : leA a b -> forall x y:list A, Ltl (a :: x) (b :: y) | Lt_tl (a:A) (x y:List) : Ltl x y -> Ltl (a :: x) (a :: y).
Inductive Desc : List -> Prop := | d_nil : Desc Nil | d_one (x:A) : Desc (x :: Nil) | d_conc (x y:A) (l:List) : leA x y -> Desc (l ++ y :: Nil) -> Desc ((l ++ y :: Nil) ++ x :: Nil).
Definition Pow : Set := sig Desc.
Definition lex_exp (a b:Pow) : Prop := Ltl (proj1_sig a) (proj1_sig b).
End Lexicographic_Exponentiation.
Section Wf_Lexicographic_Exponentiation.
Variable A : Set.
Variable leA : A -> A -> Prop.
Notation Power := (Pow A leA).
Notation Lex_Exp := (lex_exp A leA).
Notation ltl := (Ltl A leA).
Notation Descl := (Desc A leA).
Notation List := (list A).
Notation Nil := (nil (A:=A)).
Notation Cons := (cons (A:=A)).
Notation "<< x , y >>" := (exist Descl x y) (at level 0, x, y at level 100).
End Wf_Lexicographic_Exponentiation.

Lemma desc_end : forall (a b:A) (x:List), Descl (x ++ Cons a Nil) /\ ltl (x ++ Cons a Nil) (Cons b Nil) -> clos_trans A leA a b.
Proof.
intros a b x.
case x.
simpl.
simple induction 1.
intros.
inversion H1; auto with sets.
inversion H3.
simple induction 1.
generalize (app_comm_cons l (Cons a Nil) a0).
intros E; rewrite <- E; intros.
generalize (desc_tail l a a0 H0); intro.
inversion H1.
apply t_trans with (y := a0); auto with sets.
inversion H4.
