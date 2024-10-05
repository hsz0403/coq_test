Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss compiler.
Set Implicit Arguments.
Section comp.
Variable (X Y : Set) (* X is a small type of source instructions and Y of destination instructions *) (icomp : (nat -> nat) -> nat -> X -> list Y) (* instruction compiler w.r.t. a given linker & a position icomp lnk i x compiles instruction x at position i using linker lnk into a list of target instructions *) (ilen : X -> nat) (* compiled code length does not depend on linker or position, it only depends on the original instruction whether this assumption is strong or not is debatable but we only encountered cases which satisfy this assuption *) (Hilen : forall lnk n x, length (icomp lnk n x) = ilen x) (*Hilen2 : forall x, 1 <= ilen x*).
Variables (state_X state_Y : Type) (step_X : X -> (nat*state_X) -> (nat*state_X) -> Prop) (step_Y : Y -> (nat*state_Y) -> (nat*state_Y) -> Prop).
Notation "ρ '/X/' s -1> t" := (step_X ρ s t) (at level 70, no associativity).
Notation "P '/X/' s '-[' k ']->' t" := (sss_steps step_X P k s t) (at level 70, no associativity).
Notation "P '/X/' s '-+>' t" := (sss_progress step_X P s t) (at level 70, no associativity).
Notation "P '/X/' s ->> t" := (sss_compute step_X P s t) (at level 70, no associativity).
Notation "P '/X/' s '~~>' t" := (sss_output step_X P s t) (at level 70, no associativity).
Notation "P '/X/' s ↓" := (sss_terminates step_X P s)(at level 70, no associativity).
Notation "ρ '/Y/' s -1> t" := (step_Y ρ s t) (at level 70, no associativity).
Notation "P '/Y/' s '-[' k ']->' t" := (sss_steps step_Y P k s t) (at level 70, no associativity).
Notation "P '/Y/' s '-+>' t" := (sss_progress step_Y P s t) (at level 70, no associativity).
Notation "P '/Y/' s ->> t" := (sss_compute step_Y P s t) (at level 70, no associativity).
Notation "P '/Y/' s '~~>' t" := (sss_output step_Y P s t) (at level 70, no associativity).
Notation "P '/Y/' s ↓" := (sss_terminates step_Y P s)(at level 70, no associativity).
Hypothesis (step_X_tot : forall I st1, exists st2, I /X/ st1 -1> st2) (step_Y_fun : forall I st st1 st2, I /Y/ st -1> st1 -> I /Y/ st -1> st2 -> st1 = st2).
Variable (simul : state_X -> state_Y -> Prop).
Infix "⋈" := simul (at level 70, no associativity).
Definition instruction_compiler_sound := forall lnk I i1 v1 i2 v2 w1, I /X/ (i1,v1) -1> (i2,v2) -> lnk (1+i1) = length (icomp lnk i1 I) + lnk i1 -> v1 ⋈ w1 -> exists w2, (lnk i1,icomp lnk i1 I) /Y/ (lnk i1,w1) -+> (lnk i2,w2) /\ v2 ⋈ w2.
Hypothesis Hicomp : instruction_compiler_sound.
Section correctness.
Variables (linker : nat -> nat) (P : nat * list X) (Q : nat * list Y) (HPQ : forall i I, (i,I::nil) <sc P -> (linker i, icomp linker i I) <sc Q /\ linker (1+i) = ilen I + linker i).
Local Lemma compiler_complete_step p st1 w1 w3 : snd st1 ⋈ snd w1 -> linker (fst st1) = fst w1 -> in_code (fst st1) P -> out_code (fst w3) Q -> Q /Y/ w1 -[p]-> w3 -> exists q st2 w2, snd st2 ⋈ snd w2 /\ linker (fst st2) = fst w2 /\ P /X/ st1 ->> st2 /\ Q /Y/ w2 -[q]-> w3 /\ q < p.
Proof.
revert st1 w1 w3; intros (i1,v1) (j1,w1) (j3,w3); simpl fst; simpl snd.
intros H1 H2 H3 H4 H5.
destruct (in_code_subcode H3) as (I & HI).
destruct HPQ with (1 := HI) as (H6 & H7).
assert (out_code j3 (linker i1, icomp linker i1 I)) as G2.
{
revert H4; apply subcode_out_code; auto.
}
assert (H8 : ilen I <> 0).
{
intros H.
destruct (step_X_tot I (i1,v1)) as ((i2,v2) & Hst).
apply (Hicomp linker) with (3 := H1) in Hst; auto.
2: rewrite Hilen; auto.
destruct Hst as (w2 & (q & Hq1 & Hq2) & _).
rewrite <- (Hilen linker i1) in H.
destruct (icomp linker i1 I); try discriminate.
apply sss_steps_stall, proj1 in Hq2; simpl; lia.
}
assert (in_code (linker i1) (linker i1, icomp linker i1 I)) as G3.
{
simpl; rewrite (Hilen linker i1 I); lia.
}
rewrite <- H2 in H5.
destruct (step_X_tot I (i1,v1)) as ((i2,v2) & G4).
destruct (Hicomp linker) with (1 := G4) (3 := H1) as (w2 & G5 & G6).
*
rewrite H7, Hilen; auto.
*
apply subcode_sss_progress_inv with (3 := H6) (4 := G5) in H5; auto.
destruct H5 as (q & H5 & G7).
exists q, (i2,v2), (linker i2, w2); simpl; repeat (split; auto).
apply subcode_sss_compute with (1 := HI).
exists 1; apply sss_steps_1.
exists i1, nil, I, nil, v1; repeat (split; auto).
f_equal; simpl; lia.
End correctness.
Variable (P : nat * list X) (iQ : nat).
Let iP := fst P.
Let cP := snd P.
Let err := iQ+length_compiler ilen cP.
Definition gen_linker := linker ilen (iP,cP) iQ err.
Definition gen_compiler := compiler icomp ilen (iP,cP) iQ err.
Notation cQ := gen_compiler.
Notation lnk := gen_linker.
Let P_eq : P = (iP,cP).
Proof.
unfold iP, cP; destruct P; auto.
Fact gen_linker_out i : out_code i (iP,cP) -> lnk i = iQ+length cQ.
Proof.
intros H.
unfold lnk.
rewrite linker_out_err; unfold err; simpl; auto.
*
unfold cQ; rewrite compiler_length; auto.
*
lia.
End comp.

Corollary gen_compiler_output v w i' v' : v ⋈ w -> (iP,cP) /X/ (iP,v) ~~> (i',v') -> exists w', (iQ,gen_compiler) /Y/ (iQ,w) ~~> (code_end (iQ,cQ),w') /\ v' ⋈ w'.
Proof.
intros H H1.
destruct gen_compiler_sound with (1 := conj H H1) as (w1 & H2 & H3).
exists w1.
simpl; rewrite <- gen_linker_out with i'.
+
rewrite <- (linker_code_start ilen (iP,cP) iQ err) at 2; auto.
+
apply H1.
