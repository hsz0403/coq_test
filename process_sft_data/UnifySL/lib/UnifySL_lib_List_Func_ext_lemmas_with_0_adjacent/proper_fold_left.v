Require Import Coq.Classes.Morphisms.
Require Import Coq.Sorting.Permutation.
Require Export Coq.Relations.Relation_Definitions.
Require Import Logic.lib.Relation_ext.
Require Import Logic.lib.Equivalence_ext.
Require Export Coq.Lists.List.
Local Open Scope equiv_scope.
Section ListFun2.
Context {A B: Type}.
Context {RA: relation A}.
Context {RB: relation B}.
Context {EqRA: Equivalence RA}.
Context {EqRB: Equivalence RB}.
Instance proper_fold_left: forall (f: A -> B -> A) {Proper_f: Proper (equiv ==> equiv ==> equiv) f}, Proper (Forall2 equiv ==> equiv ==> equiv) (fold_left f).
Proof.
intros.
hnf; intros.
induction H; hnf; intros; simpl.
+
auto.
+
apply IHForall2.
apply Proper_f; auto.
End ListFun2.
Existing Instance proper_fold_left.
Section ListFun1.
Context {A: Type}.
Context {RA: relation A}.
Context {EqRA: Equivalence RA}.
End ListFun1.
Section ListFun2'.
Context {A B: Type}.
Context {RA: relation A}.
Context {RB: relation B}.
Instance proper_fold_left': forall (f: A -> B -> A) {Proper_f: Proper (RA ==> RB ==> RA) f}, Proper (Forall2 RB ==> RA ==> RA) (fold_left f).
Proof.
intros.
hnf; intros.
induction H; hnf; intros; simpl.
+
auto.
+
apply IHForall2.
apply Proper_f; auto.
Context {EqRA: Equivalence RA}.
End ListFun2'.
Definition not_nil {A: Type} (l: list A): Prop := l <> nil.
Instance Proper_perm_not_nil {A: Type}: Proper (@Permutation A ==> iff) (@not_nil A).
Proof.
hnf; intros.
induction H; unfold not_nil in *.
+
reflexivity.
+
split; intros ? ?; congruence.
+
split; intros ? ?; congruence.
+
tauto.
Definition semi_group_fold {A: Type} (default: A) (f: A -> A -> A) (l: list A): A := match l with | nil => default | a :: l0 => fold_left f l0 a end.
Section ListFun1'.
Context {A: Type}.
Context {RA: relation A}.
Context {EqRA: Equivalence RA}.
Instance proper_semi_group_fold: forall (f: A -> A -> A) (default: A) {Proper_f: Proper (equiv ==> equiv ==> equiv) f}, Proper (Forall2 equiv ==> equiv) (semi_group_fold default f).
Proof.
intros.
hnf; intros.
destruct H.
+
reflexivity.
+
simpl.
apply proper_fold_left; auto.
End ListFun1'.

Instance proper_fold_left: forall (f: A -> B -> A) {Proper_f: Proper (equiv ==> equiv ==> equiv) f}, Proper (Forall2 equiv ==> equiv ==> equiv) (fold_left f).
Proof.
intros.
hnf; intros.
induction H; hnf; intros; simpl.
+
auto.
+
apply IHForall2.
apply Proper_f; auto.
