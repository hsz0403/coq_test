Require Import List.
Import ListNotations.
Inductive formula : Set := | var : nat -> formula | arr : formula -> formula -> formula.
Fixpoint substitute (ζ: nat -> formula) (t: formula) : formula := match t with | var n => ζ n | arr s t => arr (substitute ζ s) (substitute ζ t) end.
Inductive hsc (Gamma: list formula) : formula -> Prop := | hsc_var : forall (ζ: nat -> formula) (t: formula), In t Gamma -> hsc Gamma (substitute ζ t) | hsc_arr : forall (s t : formula), hsc Gamma (arr s t) -> hsc Gamma s -> hsc Gamma t.
Definition HSC_PRV (Gamma: list formula) (s: formula) := hsc Gamma s.
Definition a_b_a : formula := arr (var 0) (arr (var 1) (var 0)).
Definition HSC_AX_PROBLEM := { Gamma: list formula | forall s, In s Gamma -> hsc [a_b_a] s}.
Definition HSC_AX (l: HSC_AX_PROBLEM) := hsc (proj1_sig l) a_b_a.