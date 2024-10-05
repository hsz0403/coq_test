Require Import Setoid Morphisms.
Local Set Implicit Arguments.
Local Unset Strict Implicit.
Inductive Acz : Type := Asup : forall A : Type, (A -> Acz) -> Acz.
Arguments Asup _ _ : clear implicits.
Definition pi1 s := match s with Asup A f => A end.
Definition pi2 s : (pi1 s) -> Acz := match s with Asup A f => f end.
Arguments pi2 _ : clear implicits.
Fixpoint Aeq s t := match s, t with Asup A f, Asup B g => (forall a, exists b, Aeq (f a) (g b)) /\ (forall b, exists a, Aeq (f a) (g b)) end.
Hint Resolve Aeq_ref Aeq_sym Aeq_tra : core.
Instance aeq_equiv : Equivalence Aeq.
Proof.
constructor; eauto.
Definition Ain s '(Asup A f) := exists a, Aeq s (f a).
Definition ASubq s t := forall u, Ain u s -> Ain u t.
Instance Ain_proper : Proper (Aeq ==> Aeq ==> iff) Ain.
Proof.
intros s s' H1 t t' H2.
split; intros H.
-
now apply (Ain_mor H1 H2).
-
apply Aeq_sym in H1.
apply Aeq_sym in H2.
now apply (Ain_mor H1 H2).
Instance ASubq_proper : Proper (Aeq ==> Aeq ==> iff) ASubq.
Proof.
intros s s' H1 t t' H2.
split; intros H.
-
intros u.
rewrite <- H1, <- H2.
apply H.
-
intros u.
rewrite H1, H2.
apply H.
Definition AEmpty := Asup False (fun a => match a with end).
Definition Aupair X Y := Asup bool (fun a => if a then X else Y).
Definition Aunion '(Asup A f) := Asup (sigT (fun (a : A) => (pi1 (f a)))) (fun p => let (a, b) := p in pi2 (f a) b).
Definition Apower '(Asup A f) := Asup (A -> Prop) (fun P => Asup (sig P) (fun p => let (a, _) := p in f a)).
Definition Asep (P : Acz -> Prop) '(Asup A f) := Asup (sig (fun a => P (f a))) (fun p => let (a, _) := p in f a).
Definition Arepl (F : Acz -> Acz) '(Asup A f) := Asup A (fun a => F (f a)).
Definition Asucc X := Aunion (Aupair X (Aupair X X)).
Fixpoint Anumeral n := match n with | 0 => AEmpty | S n => Asucc (Anumeral n) end.
Definition Aom := Asup nat Anumeral.
Instance Aupair_proper : Proper (Aeq ==> Aeq ==> Aeq) Aupair.
Proof.
intros s s' H1 t t' H2.
apply Aeq_ext; intros z H.
-
now apply (Aupair_mor H1 H2).
-
symmetry in H1, H2.
now apply (Aupair_mor H1 H2).
Instance Aunion_proper : Proper (Aeq ==> Aeq) Aunion.
Proof.
intros s s' H1.
apply Aeq_ext; intros z H.
-
now apply (Aunion_mor H1).
-
symmetry in H1.
now apply (Aunion_mor H1).
Instance Apower_proper : Proper (Aeq ==> Aeq) Apower.
Proof.
intros s s' H1.
apply Aeq_ext; intros z H.
-
now apply (Apower_mor H1).
-
symmetry in H1.
now apply (Apower_mor H1).
Definition cres X (R : X -> X -> Prop) (P : X -> Prop) := forall x y, R x y -> P x -> P y.
Definition fres X (R : X -> X -> Prop) (f : X -> X) := forall x y, R x y -> R (f x) (f y).
Instance Asucc_proper : Proper (Aeq ==> Aeq) Asucc.
Proof.
intros s s' H1.
unfold Asucc.
now rewrite H1.
Definition Ainductive X := Ain AEmpty X /\ forall s, Ain s X -> Ain (Asucc s) X.

Lemma Arepl_proper (F : Acz -> Acz) s s' : fres Aeq F -> Aeq s s' -> Aeq (Arepl F s) (Arepl F s').
Proof.
intros H1 H2.
now apply Arepl_proper'.
