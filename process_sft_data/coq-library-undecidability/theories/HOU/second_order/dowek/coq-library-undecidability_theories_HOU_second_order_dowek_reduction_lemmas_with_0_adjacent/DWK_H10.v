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
