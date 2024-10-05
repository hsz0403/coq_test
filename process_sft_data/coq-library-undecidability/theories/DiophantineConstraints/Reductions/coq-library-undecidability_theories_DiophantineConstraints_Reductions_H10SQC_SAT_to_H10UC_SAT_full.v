Require Import List Lia.
Import ListNotations.
Require Import Undecidability.DiophantineConstraints.H10C.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Module Argument.
Definition encode '(x, y) : nat := y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).
Definition decode (n : nat) : nat * nat := nat_rec _ (0, 0) (fun _ '(x, y) => if x is S x then (x, S y) else (S y, 0)) n.
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
by rewrite (IH (S x, y)) /= -?H ?PeanoNat.Nat.add_succ_r.
Qed.
Opaque encode decode.
Lemma ForallE {X : Type} {P : X -> Prop} {l} : Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof.
by case.
Qed.
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
by move=> /ForallE [? /IH ?].
Qed.
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
Lemma h10sqc_to_h10ucs_spec {c} : h10sqc_sem φ c -> Forall (h10uc_sem φ') (h10sqc_to_h10ucs c).
Proof.
case: c => /=.
-
move=> x ?.
constructor; last done.
rewrite /= /ζ /φ' /v ?decode_encode /=.
by lia.
-
move=> x y z ?.
(do ? constructor); rewrite /= /ζ /φ' /θ ?decode_encode /=; by nia.
-
move=> x y ?.
(do ? constructor); rewrite /= /ζ /φ' ?decode_encode /=; by nia.
Qed.
End Transport.
Lemma transport : H10SQC_SAT sqcs -> H10UC_SAT ucs.
Proof.
move=> [φ Hφ].
exists (φ' φ).
move: Hφ.
rewrite -?Forall_forall /ucs Forall_app Forall_flat_map_iff.
move=> H.
constructor.
-
by do ? constructor.
-
apply: Forall_impl H => ?.
by move /h10sqc_to_h10ucs_spec.
Qed.
Section InverseTransport.
Context (φ' : nat -> nat) (Hφ': forall c, In c ucs -> h10uc_sem φ' c).
Definition φ (x: nat) := φ' (ζ x 0).
Lemma v_spec : φ' (v 0) = 0 /\ φ' (v 1) = 1.
Proof using Hφ'.
move: (Hφ').
rewrite -Forall_forall /ucs Forall_app /v012.
move=> [/ForallE [+]] /ForallE [+] /ForallE [+] _ _ => /=.
by lia.
Qed.
Lemma h10sqc_of_h10ucs_spec {c} : Forall (h10uc_sem φ') (h10sqc_to_h10ucs c) -> h10sqc_sem φ c.
Proof using Hφ'.
case: c => /=.
-
move=> x /ForallE [].
rewrite /= ?(proj1 v_spec) /φ.
by lia.
-
move=> x y z.
do 9 (move=> /ForallE /and_comm []).
rewrite /= ?(proj1 v_spec) ?(proj2 v_spec) /φ.
by lia.
-
move=> x y /ForallE [+] /ForallE [+ _].
rewrite /= ?(proj1 v_spec) /φ.
by lia.
Qed.
End InverseTransport.
Lemma inverse_transport : H10UC_SAT ucs -> H10SQC_SAT sqcs.
Proof.
move=> [φ' Hφ'].
exists (φ φ').
move: (Hφ').
rewrite -?Forall_forall /ucs Forall_app Forall_flat_map_iff.
move=> [?].
apply: Forall_impl => ?.
by apply: h10sqc_of_h10ucs_spec.
Qed.
End Reduction.
End Argument.
Require Import Undecidability.Synthetic.Definitions.
Theorem reduction : H10SQC_SAT ⪯ H10UC_SAT.
Proof.
exists (fun sqcs => Argument.ucs sqcs) => sqcs.
constructor.
-
exact: Argument.transport.
-
exact: Argument.inverse_transport.
Qed.