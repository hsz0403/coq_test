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
Context (cs: list h10c).
Definition ζ (x: nat) := encode (x, 0).
Definition θ (x y t: nat) := encode (x, 1 + encode (y, t)).
Definition h10c_to_h10sqcs (c : h10c) : list h10sqc := match c with | h10c_one x => [h10sqc_one (ζ x)] | h10c_plus x y z => [h10sqc_plus (ζ x) (ζ y) (ζ z)] | h10c_mult x y z => [ h10sqc_sq (ζ x) (θ x y 0); h10sqc_sq (ζ y) (θ x y 1); h10sqc_plus (θ x y 0) (θ x y 1) (θ x y 2); h10sqc_plus (ζ x) (ζ y) (θ x y 3); h10sqc_sq (θ x y 3) (θ x y 4); h10sqc_plus (ζ z) (ζ z) (θ x y 5); h10sqc_plus (θ x y 2) (θ x y 5) (θ x y 4)] end.
Definition sqcs := flat_map h10c_to_h10sqcs cs.
Section Transport.
Context (φ : nat -> nat) (Hφ: forall c, In c cs -> h10c_sem c φ).
Definition φ' (n: nat) := match decode n with | (x, 0) => φ x | (x, S m) => match decode m with | (y, 0) => (φ x) * (φ x) | (y, 1) => (φ y) * (φ y) | (y, 2) => (φ x) * (φ x) + (φ y) * (φ y) | (y, 3) => (φ x) + (φ y) | (y, 4) => ((φ x) + (φ y)) * ((φ x) + (φ y)) | (y, 5) => (φ x) * (φ y) + (φ x) * (φ y) | (_, _) => 0 end end.
End Transport.
Section InverseTransport.
Context (φ' : nat -> nat) (Hφ': forall c, In c sqcs -> h10sqc_sem φ' c).
Definition φ (x: nat) := φ' (ζ x).
End InverseTransport.
End Reduction.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma transport : H10C_SAT cs -> H10SQC_SAT sqcs.
Proof.
move=> [φ Hφ].
exists (φ' φ).
move: Hφ.
rewrite -?Forall_forall /sqcs Forall_flat_map_iff.
apply: Forall_impl => ?.
by move /h10c_to_h10sqcs_spec.
