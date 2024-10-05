From Undecidability.Shared.Libs.PSL Require Import FinTypes Base.
From Undecidability.Shared.Libs.PSL Require Import Bijection.
Definition finfunc_table (A : finType) (B: Type) (f: A -> B) := List.map (fun x => (x, f x)) (elem A).
Definition lookup (A : eqType) (B : Type) (l : list (A * B)) (a : A) (def : B) : B := match (filter (fun p => Dec (fst p = a)) l) with List.nil => def | p :: _ => snd p end.

Lemma finfunc_sound_cor (A : finType) (B:Type) (f: A -> B) a b b' : (a,b) el finfunc_table f -> (a,b') el finfunc_table f -> b = b'.
Proof.
intros H1 H2.
specialize (finfunc_sound H1).
specialize (finfunc_sound H2).
congruence.
