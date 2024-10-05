Set Implicit Arguments.
Require Import RelationClasses Morphisms Wf List Lia Init.Nat Setoid.
From Undecidability.HOU Require Import calculus.calculus unification.unification.
From Undecidability.HOU.second_order Require Export diophantine_equations goldfarb.encoding goldfarb.multiplication.
Import ListNotations.
Set Default Proof Using "Type".
Section EquationEquivalences.
Variable (sigma: fin -> exp ag).
Hypothesis (N: forall x, normal (sigma x)).
Section Variables.
End Variables.
Section Constants.
Variable (n: nat) (x: nat).
Hypothesis (Ex: encodes (sigma (F x)) n).
End Constants.
Section Addition.
Variable (m n p: nat) (x y z: nat).
Hypothesis (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).
End Addition.
Section Multiplication.
Variable (m n p: nat) (x y z: nat).
Hypothesis (Ex: encodes (sigma (F x)) m) (Ey: encodes (sigma (F y)) n) (Ez: encodes (sigma (F z)) p).
End Multiplication.
End EquationEquivalences.
Section Forward.
Variables (E: list deq).
Definition gf n := lambda enc n (var 0).
Definition enc_sol (sigma: nat -> nat) (x: fin) := match partition_F_G x with | inl (exist _ x _) => gf (sigma x) | inr (exist _ (x,y,z) _) => T (sigma y) (sigma x) end.
End Forward.
Section Backward.
Definition decode_subst (sigma: fin -> exp ag) (N: forall x, normal (sigma x)) (x: fin) := match dec_enc (N (F x)) with | inl (exist _ n _) => n | inr _ => 0 end.
End Backward.
Definition nileq: eq ag := (lambda lambda a, lambda lambda a).
Definition conseqs e1 e2 := match e1, e2 with | (lambda lambda s1, lambda lambda t1), (lambda lambda s2, lambda lambda t2) => (lambda lambda g s1 s2, lambda lambda g t1 t2) | _, _ => nileq end.
Notation foldeqs := (fold_right conseqs nileq).

Lemma SU_H10 E: SOU ag 2 (H10_to_SOU E) -> H10 E.
Proof.
rewrite SOU_NSOU; (eauto 2).
intros (Delta & sigma & T & EQ & N).
exists (decode_subst sigma N).
intros e H; pose (Q := eqs e).
assert (forall p, p ∈ Q -> sigma • fst p ≡ sigma • snd p) as EQs; [|clear EQ].
-
intros [s t] G.
eapply EQ.
eapply in_Equations.
eauto.
-
destruct e; econstructor; cbn in Q, EQs.
all: specialize (EQs (varEQ x)) as EQx; mp EQx; intuition idtac; eapply backward_vars in EQx as [n EQx]; (eauto 2).
2 - 3: specialize (EQs (varEQ y)) as EQy; mp EQy; intuition idtac; eapply backward_vars in EQy as [m EQy]; (eauto 2).
2 - 3: specialize (EQs (varEQ z)) as EQz; mp EQz; intuition idtac; eapply backward_vars in EQz as [p EQz]; (eauto 2).
all: repeat (erewrite decode_subst_encodes;[|eauto]).
+
eapply backward_consts; (eauto 4).
+
eapply backward_add; (eauto 1); eapply EQs; (eauto 5).
+
eapply backward_mult; (eauto 1); eapply EQs; intuition.
