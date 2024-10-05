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
Admitted.

Lemma SET_ext : extensional SET_interp.
Proof.
intros x y.
Admitted.

Lemma SET_standard : standard SET_interp.
Proof.
intros x.
cbn.
destruct x.
unfold Som, NS, IN.
cbn.
rewrite <- (CR1 Aom).
intros [n Hn].
exists n.
rewrite <- Anumeral_numeral.
Admitted.

Lemma SET_ZF' rho : rho ⊫ ZF'.
Proof.
intros phi [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; cbn.
-
intros X Y H1 H2.
now apply set_ext.
-
apply emptyE.
-
intros X Y Z.
split; apply upairAx.
-
intros X Y.
split; apply unionAx.
-
intros X Y.
split; apply powerAx.
-
apply omAx1.
-
Admitted.

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
Admitted.

Lemma SET_rep phi rho : rho ⊨ ax_rep phi.
Proof.
intros H x.
cbn.
exists (Srep (fun u v => (u .: (v .: rho)) ⊨ phi) x).
intros y.
rewrite repAx.
-
split; intros [z[H1 H2]]; exists z; split; trivial.
+
setoid_rewrite sat_comp.
eapply sat_ext; try apply H2.
now intros [|[]].
+
setoid_rewrite sat_comp in H2.
eapply sat_ext; try apply H2.
now intros [|[]].
-
intros a b b' H1 H2.
apply (H a b b'); fold sat; eapply sat_comp, sat_ext.
2: apply H1.
3: apply H2.
Admitted.

Lemma TD_CE_normaliser : CE -> TD -> inhabited extensional_normaliser.
Proof.
intros ce [delta H].
split.
unshelve econstructor.
-
exact delta.
-
exact H.
-
intros P P' HP.
now rewrite (ce _ _ HP).
-
intros s H1 H2.
Admitted.

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
Admitted.

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
Admitted.

Lemma SET_ext' : extensional SET_interp'.
Proof.
intros x y.
Admitted.

Lemma Anumeral_numeral' n : classof (Anumeral n) = numeral n.
Proof.
induction n.
-
reflexivity.
-
cbn [Anumeral].
rewrite <- (succ_eq ce).
rewrite IHn.
Admitted.

Lemma SET_standard' : standard SET_interp'.
Proof.
intros x.
cbn.
destruct (classof_ex ce x) as [s ->].
intros [n Hn] % classof_ele.
exists n.
rewrite <- Anumeral_numeral'.
Admitted.

Lemma Anumeral_numeral n : NS (Anumeral n) = numeral n.
Proof.
induction n; trivial.
cbn [numeral].
rewrite <- IHn.
apply Aeq_NS_eq.
cbn -[Anumeral].
now rewrite <- !CR1.
