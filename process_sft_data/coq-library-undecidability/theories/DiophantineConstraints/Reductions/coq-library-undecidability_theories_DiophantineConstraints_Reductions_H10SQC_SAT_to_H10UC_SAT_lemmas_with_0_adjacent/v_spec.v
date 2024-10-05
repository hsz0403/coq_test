Require Import List Lia.
Import ListNotations.
Require Import Undecidability.DiophantineConstraints.H10C.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Definition encode '(x, y) : nat := y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).
Definition decode (n : nat) : nat * nat := nat_rec _ (0, 0) (fun _ '(x, y) => if x is S x then (x, S y) else (S y, 0)) n.
Opaque encode decode.
Section Reduction.
Context (sqcs: list h10sqc).
Definition ζ (x t: nat) := encode (1 + x, encode (0, t)).
Definition θ (x y t: nat) := encode (1 + x, encode (1 + y, t)).
Definition v (t: nat) := encode (0, t).
Definition v012 := [(v 0, v 1, v 2); (v 1, v 0, v 2); (v 0, v 0, v 1)].
Definition h10sqc_to_h10ucs (c : h10sqc) : list h10uc := match c with | h10sqc_one x => [(v 0, v 0, ζ x 0)] | h10sqc_sq x y => [(v 0, ζ x 0, ζ y 1); (ζ y 0, v 0, ζ y 1)] | h10sqc_plus x y z => [ (ζ x 0, v 0, ζ x 1); (v 0, ζ x 1, ζ x 2); (ζ x 3, ζ x 0, ζ x 2); (ζ y 0, v 0, ζ y 1); (ζ x 3, ζ y 1, θ x y 0); (θ x y 1, ζ y 0, θ x y 0); (ζ z 0, v 0, ζ z 1); (v 1, ζ z 1, θ x y 2); (θ x y 1, ζ z 0, θ x y 2)] end.
Definition ucs := v012 ++ flat_map h10sqc_to_h10ucs sqcs.
Section Transport.
Context (φ : nat -> nat) (Hφ: forall c, In c sqcs -> h10sqc_sem φ c).
Definition φ' (n: nat) := match decode n with | (0, 0) => 0 | (0, 1) => 1 | (0, 2) => 2 | (0, _) => 0 | (S x, m) => match decode m with | (0, 0) => (φ x) | (0, 1) => 1 + (φ x) | (0, 2) => 1 + (1 + (φ x)) * (1 + (φ x)) | (0, 3) => 1 + (φ x) + (φ x) | (S y, 0) => 2 + (φ x) + (φ x) + (1 + (φ y)) * (1 + (φ y)) | (S y, 1) => 2 + (φ x) + (φ x) + (φ y) + (φ y) | (S y, 2) => 2 + (1 + (φ x) + (φ y)) * (1 + (φ x) + (φ y)) | (_, _) => 0 end end.
End Transport.
Section InverseTransport.
Context (φ' : nat -> nat) (Hφ': forall c, In c ucs -> h10uc_sem φ' c).
Definition φ (x: nat) := φ' (ζ x 0).
End InverseTransport.
End Reduction.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma v_spec : φ' (v 0) = 0 /\ φ' (v 1) = 1.
Proof using Hφ'.
move: (Hφ').
rewrite -Forall_forall /ucs Forall_app /v012.
move=> [/ForallE [+]] /ForallE [+] /ForallE [+] _ _ => /=.
by lia.
