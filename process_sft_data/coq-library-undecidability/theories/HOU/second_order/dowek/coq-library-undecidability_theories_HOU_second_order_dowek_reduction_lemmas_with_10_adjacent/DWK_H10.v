Set Implicit Arguments.
Require Import List Arith Lia.
From Undecidability.HOU Require Import std.std calculus.calculus.
Import ListNotations.
From Undecidability.HOU.second_order Require Import diophantine_equations dowek.encoding.
Require Import Undecidability.HOU.unification.nth_order_unification.
Set Default Proof Using "Type".
Section EquationEquivalences.
Variable (X: Const) (sigma: fin -> exp X).
Hypothesis (N: forall x, normal (sigma x)).
Section Variables.
End Variables.
Section Constants.
Variable (x n c: nat).
Hypothesis (EQx: sigma x = enc n).
End Constants.
Section Addition.
Variable (x y z n m p c: nat).
Hypothesis (EQx: sigma x = enc m) (EQy: sigma y = enc n) (EQz: sigma z = enc p).
End Addition.
Section Multiplication.
Variable (x y z n m p c: nat).
Hypothesis (EQx: sigma x = enc m) (EQy: sigma y = enc n) (EQz: sigma z = enc p).
End Multiplication.
End EquationEquivalences.
Section Forward.
Variable (X: Const) (E: list deq).
Implicit Types (x y z: nat) (c: nat).
Definition encs theta: fin -> exp X := theta >> enc.
End Forward.
Section Backward.
Variable (X: Const).
Implicit Types (sigma: nat -> exp X) (x y z c n: nat).
Definition sub_sol sigma x := match dec_enc (sigma x) with | inl (exist _ k _) => k | inr _ => 0 end.
End Backward.

Lemma backward_vars x: sigma • fst (varEQ x) ≡ sigma • snd (varEQ x) -> exists n, sigma x = enc n.
Proof using N.
intros ?.
eapply enc_characteristic; eauto.
cbn in H.
asimpl.
asimpl in H.
unfold shift in *.
unfold funcomp at 5 in H.
asimpl in H.
rewrite <-H.
unfold funcomp at 4.
asimpl.
Admitted.

Lemma forward_consts: n = 1 -> sigma • fst (constEQ x) ≡ sigma • snd (constEQ x).
Proof using EQx.
intros; unfold constEQ, fst, snd.
subst.
Admitted.

Lemma backward_consts: sigma • fst (constEQ x) ≡ sigma • snd (constEQ x) -> n = 1.
Proof using EQx.
intros EQ; unfold constEQ, fst, snd in EQ.
asimpl in EQ.
rewrite EQx in EQ.
Admitted.

Lemma forward_add: m + n = p -> sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z).
Proof using EQz EQy EQx.
intros; unfold addEQ, fst, snd; asimpl.
Admitted.

Lemma backward_add: sigma • fst (addEQ x y z) ≡ sigma • snd (addEQ x y z) -> m + n = p.
Proof using EQz EQy EQx.
intros EQ; unfold addEQ, fst, snd in EQ; asimpl in EQ.
rewrite EQx, EQy, EQz, <-enc_add in EQ.
Admitted.

Lemma forward_mult : m * n = p -> sigma • fst (mulEQ x y z) ≡ sigma • snd (mulEQ x y z).
Proof using EQz EQy EQx.
intros; unfold mulEQ, fst, snd; asimpl.
Admitted.

Lemma backward_mult: sigma • fst (mulEQ x y z) ≡ sigma • snd (mulEQ x y z) -> m * n = p.
Proof using EQz EQy EQx.
intros EQ; unfold mulEQ, fst, snd in EQ; asimpl in EQ.
rewrite EQx, EQy, EQz, <-enc_mul in EQ.
Admitted.

Lemma forward_typing theta: nil ⊩( 3) encs theta : Gamma__dwk E.
Proof.
intros ?? <- % nth_error_In % repeated_in.
Admitted.

Lemma H10_DWK : H10 E -> SOU X 3 (H10_to_DWK X E).
Proof.
intros [theta H].
exists [].
exists (encs theta).
split.
now eapply forward_typing.
intros s t H'; cbn.
change s with (fst (s, t)); change t with (snd (s, t)) at 2.
remember (s,t) as q.
clear Heqq.
cbn in *.
eapply in_Equations in H' as (e & ? & ?).
eapply H in H0.
destruct e; cbn in *; intuition; subst.
all: try eapply forward_add.
all: try eapply forward_consts.
all: try eapply forward_mult.
all: try eapply forward_vars.
all: unfold encs, funcomp; eauto.
try eapply enc_sol_encodes.
Admitted.

Lemma sub_sol_enc sigma x n: sigma x = enc n -> sub_sol sigma x = n.
Proof.
intros H; unfold sub_sol; destruct dec_enc as [[m H']|H'].
rewrite H' in H; eapply enc_injective in H; eauto.
Admitted.

Lemma Dowek X : H10 ⪯ SOU X 3.
Proof.
exists (H10_to_DWK X).
intros E.
Admitted.

Lemma DWK_H10 E: SOU X 3 (H10_to_DWK X E) -> H10 E.
Proof.
rewrite SOU_NSOU; eauto.
intros (Delta & tau & T & EQ & N).
exists (sub_sol tau).
assert (forall e, e ∈ Eqs E -> tau • fst e ≡ tau • snd e) as H by now intros []; eauto.
intros e Hin.
destruct e; econstructor.
all: edestruct (@in_Equations X (varEQ x) E) as [_ EQx]; mp EQx; [eexists; intuition eauto; cbn; intuition | eapply H in EQx].
2, 3: edestruct (@in_Equations X (varEQ y) E) as [_ EQy]; mp EQy; [eexists; intuition eauto; cbn; intuition| eapply H in EQy].
2, 3: edestruct (@in_Equations X (varEQ z) E) as [_ EQz]; mp EQz; [eexists; intuition eauto; cbn; intuition| eapply H in EQz].
all: eapply backward_vars in EQx as [n]; eauto.
2 - 3: eapply backward_vars in EQy as [m]; eauto.
2 - 3: eapply backward_vars in EQz as [p]; eauto.
all: repeat (erewrite sub_sol_enc; [|eauto]).
-
eapply backward_consts; eauto.
eapply H, in_Equations; eexists; intuition eauto.
cbn; intuition.
-
eapply backward_add; eauto.
eapply H, in_Equations; eexists; intuition eauto.
cbn; intuition.
-
eapply backward_mult; eauto.
eapply H, in_Equations; eexists; intuition eauto.
cbn; intuition.
