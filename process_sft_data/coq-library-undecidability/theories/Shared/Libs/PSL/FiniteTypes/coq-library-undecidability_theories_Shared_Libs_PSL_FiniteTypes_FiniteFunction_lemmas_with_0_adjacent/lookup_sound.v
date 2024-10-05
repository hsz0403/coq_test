From Undecidability.Shared.Libs.PSL Require Import FinTypes Base.
From Undecidability.Shared.Libs.PSL Require Import Bijection.
Definition finfunc_table (A : finType) (B: Type) (f: A -> B) := List.map (fun x => (x, f x)) (elem A).
Definition lookup (A : eqType) (B : Type) (l : list (A * B)) (a : A) (def : B) : B := match (filter (fun p => Dec (fst p = a)) l) with List.nil => def | p :: _ => snd p end.

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
dec; cbn in *; subst; firstorder.
