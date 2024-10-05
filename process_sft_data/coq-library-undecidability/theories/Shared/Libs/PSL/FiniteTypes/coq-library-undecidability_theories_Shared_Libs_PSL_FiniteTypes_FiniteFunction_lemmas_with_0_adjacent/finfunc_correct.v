From Undecidability.Shared.Libs.PSL Require Import FinTypes Base.
From Undecidability.Shared.Libs.PSL Require Import Bijection.
Definition finfunc_table (A : finType) (B: Type) (f: A -> B) := List.map (fun x => (x, f x)) (elem A).
Definition lookup (A : eqType) (B : Type) (l : list (A * B)) (a : A) (def : B) : B := match (filter (fun p => Dec (fst p = a)) l) with List.nil => def | p :: _ => snd p end.

Lemma finfunc_correct (A: finType) B (f: A -> B) a def: lookup (finfunc_table f) a def = f a.
Proof.
eapply lookup_sound; [ apply finfunc_sound_cor | apply finfunc_comp ].
