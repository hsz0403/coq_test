From Undecidability.FOL Require Import binZF ZF Reductions.PCPb_to_ZF.
From Undecidability.FOL Require Import Aczel Aczel_CE Aczel_TD Syntax FullTarski_facts.
Section ZFM.
Context { Delta : extensional_normaliser }.
Instance SET_interp : interp SET.
Proof.
split; intros [].
-
intros _.
exact Sempty.
-
intros v.
exact (Supair (Vector.hd v) (Vector.hd (Vector.tl v))).
-
intros v.
exact (Sunion (Vector.hd v)).
-
intros v.
exact (Spower (Vector.hd v)).
-
intros _.
exact Som.
-
intros v.
exact (IN (Vector.hd v) (Vector.hd (Vector.tl v))).
-
intros v.
exact (Vector.hd v = Vector.hd (Vector.tl v)).
Defined.
End ZFM.
Definition TD := exists delta : (Acz -> Prop) -> Acz, forall P, (exists s : Acz, forall t : Acz, P t <-> Aeq t s) -> P (delta P).
Section ZM.
Hypothesis ce : CE.
Instance SET_interp' : interp SET'.
Proof.
split; intros [].
-
intros _.
exact empty.
-
intros v.
exact (upair ce (Vector.hd v) (Vector.hd (Vector.tl v))).
-
intros v.
exact (union ce (Vector.hd v)).
-
intros v.
exact (power ce (Vector.hd v)).
-
intros _.
exact om.
-
intros v.
exact (ele (Vector.hd v) (Vector.hd (Vector.tl v))).
-
intros v.
exact (Vector.hd v = Vector.hd (Vector.tl v)).
Defined.
End ZM.
Section IM.
Instance Acz_interp : interp Acz.
Proof.
split; intros [].
-
intros _.
exact AEmpty.
-
intros v.
exact (Aupair (Vector.hd v) (Vector.hd (Vector.tl v))).
-
intros v.
exact (Aunion (Vector.hd v)).
-
intros v.
exact (Apower (Vector.hd v)).
-
intros _.
exact Aom.
-
intros v.
exact (Ain (Vector.hd v) (Vector.hd (Vector.tl v))).
-
intros v.
exact (Aeq (Vector.hd v) (Vector.hd (Vector.tl v))).
Defined.
End IM.

Lemma normaliser_model : CE -> TD -> exists V (M : interp V), extensional M /\ standard M /\ forall rho psi, ZF psi -> rho ⊨ psi.
Proof.
intros H1 H2.
assert (inhabited extensional_normaliser) as [H] by now apply TD_CE_normaliser.
exists SET, SET_interp.
split; try apply SET_ext.
split; try apply SET_standard.
intros rho psi [].
-
now apply SET_ZF'.
-
apply SET_sep.
-
apply SET_rep.
