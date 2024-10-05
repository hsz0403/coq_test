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

Lemma Aeq_ASubq s t : Aeq s t -> ASubq s t.
Proof.
destruct s as [A f], t as [B g].
intros [H _] z [a Z].
destruct (H a) as [b I].
exists b.
Admitted.

Lemma AEmptyAx s : ~ Ain s AEmpty.
Proof.
Admitted.

Lemma AupairAx s t u : Ain u (Aupair s t) <-> Aeq u s \/ Aeq u t.
Proof.
split; intros H.
-
destruct H as [[] H]; auto.
-
Admitted.

Lemma Aupair_mor s s' t t' u : Aeq s s' -> Aeq t t' -> Ain u (Aupair s t) -> Ain u (Aupair s' t').
Proof.
intros H1 H2 H.
apply AupairAx.
rewrite <- H1, <- H2.
Admitted.

Instance Aupair_proper : Proper (Aeq ==> Aeq ==> Aeq) Aupair.
Proof.
intros s s' H1 t t' H2.
apply Aeq_ext; intros z H.
-
now apply (Aupair_mor H1 H2).
-
symmetry in H1, H2.
Admitted.

Lemma AunionAx s u : Ain u (Aunion s) <-> exists t, Ain t s /\ Ain u t.
Proof.
split; intros H; destruct s as [A f].
-
destruct H as [[a b] H].
exists (f a).
split.
+
now exists a.
+
destruct (f a) as [C h]; simpl in *.
now exists b.
-
destruct H as [[B g][[a Z1][b Z2]]].
apply Aeq_ASubq in Z1.
specialize (Z1 (g b) (Ain_Asup g b)).
apply Ain_pi in Z1 as [c H].
exists (existT _ a c).
Admitted.

Lemma Aunion_mor s s' u : Aeq s s' -> Ain u (Aunion s) -> Ain u (Aunion s').
Proof.
intros H1 H2.
apply AunionAx in H2 as [t H2].
rewrite H1 in H2.
apply AunionAx.
Admitted.

Instance Aunion_proper : Proper (Aeq ==> Aeq) Aunion.
Proof.
intros s s' H1.
apply Aeq_ext; intros z H.
-
now apply (Aunion_mor H1).
-
symmetry in H1.
Admitted.

Lemma ApowerAx s t : Ain t (Apower s) <-> ASubq t s.
Proof.
split; intros H; destruct s as [A f].
-
destruct H as [P H].
intros u Z.
apply Aeq_ASubq in H.
destruct (H u Z) as [[a PA] I].
now exists a.
-
exists (fun a => Ain (f a) t).
apply Aeq_ext; intros z Z.
+
destruct t as [B g], Z as [b H1].
destruct (H (g b) (Ain_Asup g b)) as [a J].
assert (H2: Ain (f a) (Asup B g)) by (exists b; auto).
exists (exist _ a H2).
eauto.
+
destruct Z as [[a YA] H1 % Aeq_sym].
Admitted.

Lemma Apower_mor s s' t : Aeq s s' -> Ain t (Apower s) -> Ain t (Apower s').
Proof.
intros H1 H2.
apply ApowerAx.
rewrite <- H1.
Admitted.

Instance Apower_proper : Proper (Aeq ==> Aeq) Apower.
Proof.
intros s s' H1.
apply Aeq_ext; intros z H.
-
now apply (Apower_mor H1).
-
symmetry in H1.
Admitted.

Lemma AsepAx (P : Acz -> Prop) s t : cres Aeq P -> Ain t (Asep P s) <-> Ain t s /\ P t.
Proof.
intros HP.
split; intros H; destruct s as [A f].
-
destruct H as [[a PA]H].
split; eauto.
now exists a.
-
destruct H as [[a H]PY].
assert (PA : P (f a)) by now apply (HP t).
Admitted.

Lemma Asep_mor (P P' : Acz -> Prop) s s' t : cres Aeq P -> cres Aeq P' -> (forall s, P s <-> P' s) -> Aeq s s' -> Ain t (Asep P s) -> Ain t (Asep P' s').
Proof.
intros H1 H2 H3 H4 H5.
apply AsepAx; trivial.
rewrite <- H3, <- H4.
Admitted.

Lemma Asep_proper' (P P' : Acz -> Prop) s s' : cres Aeq P -> cres Aeq P' -> (forall s, P s <-> P' s) -> Aeq s s' -> Aeq (Asep P s) (Asep P' s').
Proof.
intros H1 H2 H3 H4.
apply Aeq_ext; intros z Z.
-
apply (Asep_mor H1 H2 H3 H4); assumption.
-
Admitted.

Lemma Asep_proper (P : Acz -> Prop) s s' : cres Aeq P -> Aeq s s' -> Aeq (Asep P s) (Asep P s').
Proof.
intros H1 H2.
Admitted.

Lemma AreplAx F s u : fres Aeq F -> Ain u (Arepl F s) <-> exists t, Ain t s /\ Aeq u (F t).
Proof.
intros HF.
split; intros H; destruct s as [A f].
-
destruct H as [a H].
exists (f a).
split; trivial.
apply Ain_Asup.
-
destruct H as [z[[a H] Z]].
exists a.
apply HF in H; try now exists a.
Admitted.

Lemma Arepl_mor (F F' : Acz -> Acz) s s' u : fres Aeq F -> fres Aeq F' -> (forall s, Aeq (F s) (F' s)) -> Aeq s s' -> Ain u (Arepl F s) -> Ain u (Arepl F' s').
Proof.
intros H1 H2 H3 H4 H5.
apply AreplAx; trivial.
apply AreplAx in H5 as [y H]; trivial.
exists y.
Admitted.

Lemma Arepl_proper' (F F' : Acz -> Acz) s s' : fres Aeq F -> fres Aeq F' -> (forall s, Aeq (F s) (F' s)) -> Aeq s s' -> Aeq (Arepl F s) (Arepl F' s').
Proof.
intros H1 H2 H3 H4.
apply Aeq_ext; intros z Z.
-
apply (Arepl_mor H1 H2 H3 H4); assumption.
-
Admitted.

Lemma Arepl_proper (F : Acz -> Acz) s s' : fres Aeq F -> Aeq s s' -> Aeq (Arepl F s) (Arepl F s').
Proof.
intros H1 H2.
Admitted.

Instance Asucc_proper : Proper (Aeq ==> Aeq) Asucc.
Proof.
intros s s' H1.
unfold Asucc.
Admitted.

Lemma AomAx2 X : Ainductive X -> ASubq Aom X.
Proof.
intros H s [n ->].
Admitted.

Lemma AomAx1 : Ainductive Aom.
Proof.
split.
-
exists 0.
apply Aeq_ref.
-
intros s [n H].
exists (S n).
now rewrite H.
