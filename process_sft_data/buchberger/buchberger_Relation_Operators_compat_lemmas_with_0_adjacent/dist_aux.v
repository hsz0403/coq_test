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

Lemma dist_aux : forall z:List, Descl z -> forall x y:List, z = x ++ y -> Descl x /\ Descl y.
Proof.
intros z D.
elim D.
intros.
cut (x ++ y = Nil); auto with sets; intro.
generalize (app_eq_nil _ _ H0); simple induction 1.
intros.
rewrite H2; rewrite H3; split; apply d_nil.
intros.
cut (x0 ++ y = Cons x Nil); auto with sets.
intros E.
generalize (app_eq_unit _ _ E); simple induction 1.
simple induction 1; intros.
rewrite H2; rewrite H3; split.
apply d_nil.
apply d_one.
simple induction 1; intros.
rewrite H2; rewrite H3; split.
apply d_one.
apply d_nil.
do 5 intro.
intros Hind.
do 2 intro.
generalize x0.
apply rev_ind with (A := A) (P := fun y0:List => forall x0:List, (l ++ Cons y Nil) ++ Cons x Nil = x0 ++ y0 -> Descl x0 /\ Descl y0).
intro.
generalize (app_nil_end x1); simple induction 1; simple induction 1.
split.
apply d_conc; auto with sets.
apply d_nil.
do 3 intro.
generalize x1.
apply rev_ind with (A := A) (P := fun l0:List => forall (x1:A) (x0:List), (l ++ Cons y Nil) ++ Cons x Nil = x0 ++ l0 ++ Cons x1 Nil -> Descl x0 /\ Descl (l0 ++ Cons x1 Nil)).
simpl.
split.
generalize (app_inj_tail _ _ _ _ H2); simple induction 1.
simple induction 1; auto with sets.
apply d_one.
do 5 intro.
generalize (app_ass x4 (l1 ++ Cons x2 Nil) (Cons x3 Nil)).
simple induction 1.
generalize (app_ass x4 l1 (Cons x2 Nil)); simple induction 1.
intro E.
generalize (app_inj_tail _ _ _ _ E).
simple induction 1; intros.
generalize (app_inj_tail _ _ _ _ H6); simple induction 1; intros.
rewrite <- H7; rewrite <- H10; generalize H6.
generalize (app_ass x4 l1 (Cons x2 Nil)); intro E1.
rewrite E1.
intro.
generalize (Hind x4 (l1 ++ Cons x2 Nil) H11).
simple induction 1; split.
auto with sets.
generalize H14.
rewrite <- H10; intro.
apply d_conc; auto with sets.
