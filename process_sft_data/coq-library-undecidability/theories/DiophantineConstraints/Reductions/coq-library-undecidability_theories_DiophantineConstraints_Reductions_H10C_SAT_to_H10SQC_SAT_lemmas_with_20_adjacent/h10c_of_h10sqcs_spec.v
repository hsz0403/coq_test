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

Lemma decode_encode {xy: nat * nat} : decode (encode xy) = xy.
Proof.
move Hn: (encode xy) => n.
elim: n xy Hn.
{
by move=> [[|?] [|?]].
}
move=> n IH [x [|y [H]]] /=.
{
move: x => [|x [H]] /=; first done.
by rewrite (IH (0, x)) /= -?H ?PeanoNat.Nat.add_0_r.
}
Admitted.

Lemma ForallE {X : Type} {P : X -> Prop} {l} : Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof.
Admitted.

Lemma Forall_flat_map_iff {T U: Type} {P : T -> Prop} {ds : list U} {f : U -> list T} : Forall P (flat_map f ds) <-> Forall (fun d => Forall P (f d)) ds.
Proof.
elim: ds; first by (constructor=> /=).
move=> a l IH /=.
rewrite Forall_app.
constructor.
-
move=> [? ?].
constructor; [done | by apply /IH].
-
Admitted.

Lemma h10c_to_h10sqcs_spec {c} : h10c_sem c φ -> Forall (h10sqc_sem φ') (h10c_to_h10sqcs c).
Proof.
case: c => /=.
-
move=> x ?.
constructor; last done.
by rewrite /= /ζ /φ' decode_encode.
-
move=> x y z ?.
constructor; last done.
by rewrite /= /ζ /φ' ?decode_encode.
-
move=> x y z ?.
Admitted.

Lemma transport : H10C_SAT cs -> H10SQC_SAT sqcs.
Proof.
move=> [φ Hφ].
exists (φ' φ).
move: Hφ.
rewrite -?Forall_forall /sqcs Forall_flat_map_iff.
apply: Forall_impl => ?.
Admitted.

Lemma inverse_transport : H10SQC_SAT sqcs -> H10C_SAT cs.
Proof.
move=> [φ' Hφ'].
exists (φ φ').
move: Hφ'.
rewrite -?Forall_forall /sqcs Forall_flat_map_iff.
apply: Forall_impl => ?.
Admitted.

Theorem reduction : H10C_SAT ⪯ H10SQC_SAT.
Proof.
exists (fun cs => Argument.sqcs cs) => cs.
constructor.
-
exact: Argument.transport.
-
Admitted.

Lemma h10c_of_h10sqcs_spec {c} : Forall (h10sqc_sem φ') (h10c_to_h10sqcs c) -> h10c_sem c φ.
Proof.
case: c => /=.
-
by move=> x /ForallE [].
-
by move=> x y z /ForallE [].
-
move=> x y z.
do 7 (move=> /ForallE /and_comm []).
rewrite /= /φ.
by nia.
