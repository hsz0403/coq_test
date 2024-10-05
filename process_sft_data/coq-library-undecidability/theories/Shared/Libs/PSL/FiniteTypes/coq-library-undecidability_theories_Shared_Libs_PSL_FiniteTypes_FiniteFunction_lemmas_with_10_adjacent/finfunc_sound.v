From Undecidability.Shared.Libs.PSL Require Import FinTypes Base.
From Undecidability.Shared.Libs.PSL Require Import Bijection.
Definition finfunc_table (A : finType) (B: Type) (f: A -> B) := List.map (fun x => (x, f x)) (elem A).
Definition lookup (A : eqType) (B : Type) (l : list (A * B)) (a : A) (def : B) : B := match (filter (fun p => Dec (fst p = a)) l) with List.nil => def | p :: _ => snd p end.

Lemma finfunc_comp (A : finType) (B: Type) (f: A -> B) a : (a,f a) el finfunc_table f.
Proof.
unfold finfunc_table.
Admitted.

Lemma finfunc_sound_cor (A : finType) (B:Type) (f: A -> B) a b b' : (a,b) el finfunc_table f -> (a,b') el finfunc_table f -> b = b'.
Proof.
intros H1 H2.
specialize (finfunc_sound H1).
specialize (finfunc_sound H2).
Admitted.

Lemma lookup_sound (A: eqType) (B: Type) (L : list (prod A B)) a b def : (forall a' b1 b2, (a',b1) el L -> (a',b2) el L -> b1=b2) -> (a,b) el L -> lookup L a def = b.
Proof.
intros H1 H2.
unfold lookup.
destruct filter eqn:E.
-
assert ((a,b) el filter (fun p : A * B => Dec (fst p = a)) L) by ( rewrite in_filter_iff ; eauto).
now rewrite E in H.
-
destruct p.
assert ((e,b0) el (filter (fun p : A * B => Dec (fst p = a)) L)) by now rewrite E.
rewrite in_filter_iff in H.
Admitted.

Lemma lookup_complete (A: eqType) (B: Type) (L : list (prod A B)) a def : {(a,lookup L a def) el L } + {~(exists b, (a,b) el L) /\ lookup L a def = def}.
Proof.
unfold lookup.
destruct filter eqn:E.
-
right.
split.
2:easy.
intros (x&?).
assert ((a,x) el filter (fun p : A * B => Dec (fst p = a)) L).
{
rewrite in_filter_iff;cbn.
decide _;try easy.
}
rewrite E in H0.
easy.
-
assert (p el (filter (fun p : A * B => Dec (fst p = a)) L)) by now rewrite E.
rewrite in_filter_iff in H.
destruct p.
Admitted.

Lemma finfunc_correct (A: finType) B (f: A -> B) a def: lookup (finfunc_table f) a def = f a.
Proof.
Admitted.

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
Admitted.

Lemma finfunc_sound (A : finType) (B : Type) (f: A -> B) a b: (a,b) el finfunc_table f -> b = f a.
Proof.
unfold finfunc_table.
rewrite in_map_iff.
firstorder congruence.
