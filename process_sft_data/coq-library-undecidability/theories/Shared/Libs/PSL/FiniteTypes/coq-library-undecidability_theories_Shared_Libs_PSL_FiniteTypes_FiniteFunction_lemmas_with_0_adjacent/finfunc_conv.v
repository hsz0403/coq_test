From Undecidability.Shared.Libs.PSL Require Import FinTypes Base.
From Undecidability.Shared.Libs.PSL Require Import Bijection.
Definition finfunc_table (A : finType) (B: Type) (f: A -> B) := List.map (fun x => (x, f x)) (elem A).
Definition lookup (A : eqType) (B : Type) (l : list (A * B)) (a : A) (def : B) : B := match (filter (fun p => Dec (fst p = a)) l) with List.nil => def | p :: _ => snd p end.

Lemma finfunc_conv (A: finType) (cA : eqType) (B cB : Type) (f: A -> B) (mA : A -> cA) (mB : B -> cB) a def: injective mA -> lookup (List.map (fun x => (mA (fst x), mB (snd x))) (finfunc_table f)) (mA a) def = mB (f a).
Proof.
intros INJ.
erewrite lookup_sound; eauto.
-
intros a' b1 b2 H1 H2.
rewrite in_map_iff in *.
destruct H1 as [[] [L1 R1]].
destruct H2 as [[] [L2 R2]].
cbn in *.
inv L1; inv L2.
rewrite (finfunc_sound R1), (finfunc_sound R2), (INJ e e0); congruence.
-
rewrite in_map_iff.
exists (a, f a).
subst.
split; auto.
apply finfunc_comp.
