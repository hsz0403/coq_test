From Undecidability.Shared.Libs.PSL Require Import FinTypes Base.
From Undecidability.Shared.Libs.PSL Require Import Bijection.
Definition finfunc_table (A : finType) (B: Type) (f: A -> B) := List.map (fun x => (x, f x)) (elem A).
Definition lookup (A : eqType) (B : Type) (l : list (A * B)) (a : A) (def : B) : B := match (filter (fun p => Dec (fst p = a)) l) with List.nil => def | p :: _ => snd p end.

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
dec; cbn in *; subst; firstorder.
