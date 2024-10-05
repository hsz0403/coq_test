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

Lemma desc_tail : forall (x:List) (a b:A), Descl (Cons b (x ++ Cons a Nil)) -> clos_trans A leA a b.
Proof.
intro.
apply rev_ind with (A := A) (P := fun x:List => forall a b:A, Descl (Cons b (x ++ Cons a Nil)) -> clos_trans A leA a b).
intros.
inversion H.
cut (Cons b (Cons a Nil) = (Nil ++ Cons b Nil) ++ Cons a Nil); auto with sets; intro.
generalize H0.
intro.
generalize (app_inj_tail (l ++ Cons y Nil) (Nil ++ Cons b Nil) _ _ H4); simple induction 1.
intros.
generalize (app_inj_tail _ _ _ _ H6); simple induction 1; intros.
generalize H1.
rewrite <- H10; rewrite <- H7; intro.
apply (t_step A leA); auto with sets.
intros.
inversion H0.
generalize (app_cons_not_nil _ _ _ H3); intro.
elim H1.
generalize H0.
generalize (app_comm_cons (l ++ Cons x0 Nil) (Cons a Nil) b); simple induction 1.
intro.
generalize (desc_prefix (Cons b (l ++ Cons x0 Nil)) a H5); intro.
generalize (H x0 b H6).
intro.
apply t_trans with (A := A) (y := x0); auto with sets.
apply t_step.
generalize H1.
rewrite H4; intro.
generalize (app_inj_tail _ _ _ _ H8); simple induction 1.
intros.
generalize H2; generalize (app_comm_cons l (Cons x0 Nil) b).
intro.
generalize H10.
rewrite H12; intro.
generalize (app_inj_tail _ _ _ _ H13); simple induction 1.
intros.
rewrite <- H11; rewrite <- H16; auto with sets.
