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

Lemma SET_sep phi rho : rho ⊨ ax_sep phi.
Proof.
intros x.
cbn.
exists (Ssep (fun y => (y .: rho) ⊨ phi) x).
intros y.
rewrite sepAx.
split; intros [H1 H2]; split; trivial.
-
setoid_rewrite sat_comp.
eapply sat_ext; try apply H2.
now intros [].
-
setoid_rewrite sat_comp in H2.
eapply sat_ext; try apply H2.
now intros [].
