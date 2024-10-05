Global Set Asymmetric Patterns.
Require Import Arith.
Require Import EqNat.
Require Export Reals.
Require Export Omega.
Open Scope R_scope.
Inductive dim:Set := zero : dim | one : dim.
Definition dart := nat.
Definition eq_dart_dec := eq_nat_dec.
Definition nil := 0%nat.
Open Scope Z_scope.
Inductive fmap:Set := V : fmap | I : fmap->dart->tag->point->fmap | L : fmap->dim->dart->dart->fmap.
Definition empty(m:fmap): Prop:= match m with V => True | _ => False end.
Definition inj_dart(Df:dart->Prop)(f:dart->dart):Prop:= forall x x':dart, (Df x)->(Df x')->(f x)=(f x')->x=x'.
Definition surj_dart(Df:dart->Prop)(f:dart->dart):Prop := forall y:dart, Df y -> exists x : dart, Df x /\ f x = y.
Definition bij_dart(Df:dart->Prop)(f:dart->dart):Prop:= inj_dart Df f /\ surj_dart Df f.
Fixpoint top (m:fmap)(k:dim)(z:dart){struct m}:dart:= match m with V => nil | I m0 x _ _ => if eq_dart_dec x z then z else top m0 k z | L m0 k0 x y => if eq_dim_dec k0 k then if eq_dart_dec x (top m0 k0 z) then top m0 k0 y else top m0 k0 z else top m0 k z end.
Fixpoint bottom (m:fmap)(k:dim)(z:dart){struct m}:dart:= match m with V => nil | I m0 x _ _ => if eq_dart_dec x z then z else bottom m0 k z | L m0 k0 x y => if (eq_dim_dec k0 k) then if eq_dart_dec y (bottom m0 k0 z) then bottom m0 k0 x else bottom m0 k0 z else bottom m0 k z end.

Lemma Req_dec_1 : forall r1 r2 : R, {r1 = r2} + {r1 <> r2}.
Proof.
Admitted.

Lemma eq_point_dec : forall (p q:point), {eq_point p q} + {~eq_point p q}.
Proof.
intros.
unfold eq_point in |- *.
elim p.
elim q.
simpl in |- *.
intros.
generalize (Req_dec_1 a0 a).
generalize (Req_dec_1 b0 b).
Admitted.

Lemma empty_dec: forall (m:fmap), {empty m}+{~empty m}.
Proof.
intro m.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
tauto.
right.
intro.
Admitted.

Lemma exd_dec: forall (m:fmap)(x:dart), {exd m x}+{~exd m x}.
Proof.
induction m.
right.
intro.
inversion H.
intro.
simpl.
elim (IHm x).
left.
simpl in |- *.
tauto.
intro.
elim (eq_dart_dec d x).
tauto.
tauto.
intro.
elim (IHm x).
left.
simpl in |- *.
assumption.
simpl in |- *.
Admitted.

Lemma succ_dec: forall (m:fmap)(k:dim)(x:dart), {succ m k x} + {~succ m k x}.
Proof.
intros.
unfold succ in |- *.
elim (eq_dart_dec (A m k x) nil).
tauto.
Admitted.

Lemma pred_dec: forall (m:fmap)(k:dim)(x:dart), {pred m k x} + {~pred m k x}.
Proof.
intros.
unfold pred in |- *.
elim (eq_dart_dec (A_1 m k x) nil).
tauto.
Admitted.

Lemma not_exd_nil : forall m:fmap, inv_hmap m -> ~exd m nil.
Proof.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros.
intro.
elim H0.
intro.
symmetry in H1.
tauto.
tauto.
simpl in |- *.
Admitted.

Lemma exd_not_nil : forall (m:fmap)(z:dart), inv_hmap m -> exd m z -> z <> nil.
Proof.
intros.
elim (eq_dart_dec z nil).
intro.
rewrite a in H0.
assert (~ exd m nil).
apply not_exd_nil.
tauto.
tauto.
Admitted.

Lemma succ_exd : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> succ m k z -> exd m z.
Proof.
unfold succ in |- *.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z Hinv.
elim (eq_dart_dec d z).
tauto.
intros.
right.
eapply IHm.
tauto.
apply H.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d0 z).
intros.
rewrite <- a in |- *.
tauto.
intros.
eapply IHm.
tauto.
apply H0.
intros.
eapply IHm.
tauto.
Admitted.

Lemma pred_exd : forall (m:fmap)(k:dim)(z:dart), inv_hmap m -> pred m k z -> exd m z.
Proof.
unfold pred in |- *.
induction m.
simpl in |- *.
tauto.
simpl in |- *.
unfold prec_I in |- *.
intros k z Hinv.
elim (eq_dart_dec d z).
tauto.
intros.
right.
eapply IHm.
tauto.
apply H.
intros k z.
simpl in |- *.
unfold prec_L in |- *.
elim (eq_dim_dec d k).
elim (eq_dart_dec d1 z).
intros.
rewrite <-a.
tauto.
intros.
eapply IHm.
tauto.
apply H0.
intros.
eapply IHm.
tauto.
Admitted.

Lemma eq_dim_dec : forall i k : dim, {i=k}+{~i=k}.
Proof.
double induction i k.
tauto.
right.
discriminate.
right.
discriminate.
tauto.
