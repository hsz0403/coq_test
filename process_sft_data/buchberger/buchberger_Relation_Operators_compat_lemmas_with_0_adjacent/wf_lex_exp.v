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

Theorem wf_lex_exp : well_founded leA -> well_founded Lex_Exp.
Proof.
unfold well_founded at 2.
simple induction a; intros x y.
apply Acc_intro.
simple induction y0.
unfold lex_exp at 1; simpl.
apply rev_ind with (A := A) (P := fun x:List => forall (x0:List) (y:Descl x0), ltl x0 x -> Acc Lex_Exp << x0, y >>).
intros.
inversion_clear H0.
intro.
generalize (well_founded_ind (wf_clos_trans A leA H)).
intros GR.
apply GR with (P := fun x0:A => forall l:List, (forall (x1:List) (y:Descl x1), ltl x1 l -> Acc Lex_Exp << x1, y >>) -> forall (x1:List) (y:Descl x1), ltl x1 (l ++ Cons x0 Nil) -> Acc Lex_Exp << x1, y >>).
intro; intros HInd; intros.
generalize (right_prefix x2 l (Cons x1 Nil) H1).
simple induction 1.
intro; apply (H0 x2 y1 H3).
simple induction 1.
intro; simple induction 1.
clear H4 H2.
intro; generalize y1; clear y1.
rewrite H2.
apply rev_ind with (A := A) (P := fun x3:List => forall y1:Descl (l ++ x3), ltl x3 (Cons x1 Nil) -> Acc Lex_Exp << l ++ x3, y1 >>).
intros.
generalize (app_nil_end l); intros Heq.
generalize y1.
clear y1.
rewrite <- Heq.
intro.
apply Acc_intro.
simple induction y2.
unfold lex_exp at 1.
simpl; intros x4 y3.
intros.
apply (H0 x4 y3); auto with sets.
intros.
generalize (dist_Desc_concat l (l0 ++ Cons x4 Nil) y1).
simple induction 1.
intros.
generalize (desc_end x4 x1 l0 (conj H8 H5)); intros.
generalize y1.
rewrite <- (app_ass l l0 (Cons x4 Nil)); intro.
generalize (HInd x4 H9 (l ++ l0)); intros HInd2.
generalize (ltl_unit l0 x4 x1 H8 H5); intro.
generalize (dist_Desc_concat (l ++ l0) (Cons x4 Nil) y2).
simple induction 1; intros.
generalize (H4 H12 H10); intro.
generalize (Acc_inv H14).
generalize (acc_app l l0 H12 H14).
intros f g.
generalize (HInd2 f); intro.
apply Acc_intro.
simple induction y3.
unfold lex_exp at 1; simpl; intros.
apply H15; auto with sets.
