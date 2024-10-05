Require Import Arith Lia List.
Import ListNotations.
Require Import Undecidability.SetConstraints.FMsetC.
From Undecidability.SetConstraints.Util Require Facts mset_eq_utils mset_poly_utils.
Require Undecidability.DiophantineConstraints.H10C.
Require Import Undecidability.Synthetic.Definitions.
Require Import Undecidability.Synthetic.ReducibilityFacts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Notation "A ≡ B" := (mset_eq A B) (at level 65).
Module H10UC_FMsetTC.
Inductive mset_term : Set := | mset_term_zero : mset_term | mset_term_var : nat -> mset_term | mset_term_plus : mset_term -> mset_term -> mset_term | mset_term_h : mset_term -> mset_term.
Definition constraint : Set := mset_term * mset_term.
Fixpoint mset_sem (φ : nat -> list nat) (A : mset_term) : list nat := match A with | mset_term_zero => [0] | mset_term_var x => φ x | mset_term_plus A B => (mset_sem φ A) ++ (mset_sem φ B) | mset_term_h A => map S (mset_sem φ A) end.
Definition mset_sat (φ : nat -> list nat) (l : list constraint) := Forall (fun '(A, B) => (mset_sem φ A) ≡ (mset_sem φ B)) l.
Definition FMsetTC_SAT (l: list constraint) := exists (φ : nat -> list nat), mset_sat φ l.
Import Facts mset_eq_utils mset_poly_utils.
Module Argument.
Local Notation "t ⊍ u" := (mset_term_plus t u) (at level 40).
Local Notation "'h' t" := (mset_term_h t) (at level 38).
Local Notation "•0" := mset_term_zero.
Coercion mset_term_var : nat >-> mset_term.
Fixpoint tower m n := match n with | 0 => [] | S n => (tower m n) ++ (tower m n) ++ (tower m n) ++ (tower m n) ++ [m*n] end.
Definition unify_sat n : {A | A ++ (map (fun i => 2*i) (seq 0 n)) ≡ (seq 0 n) ++ map S A}.
Proof.
elim: n; first by exists [].
set f := (fun i => 2*i).
move=> n [A HA].
exists (A ++ seq n n).
rewrite ?seq_last ?map_app /=.
apply /(eq_lr (A' := (A ++ map f (seq 0 n)) ++ (seq n n ++ [f n])) (B' := (seq 0 n ++ map S A) ++ ([n] ++ map S (seq n n)))); [by eq_trivial | by eq_trivial |].
apply: eq_appI; first done.
rewrite /f.
have ->: 2 * n = n + n by lia.
apply: eq_eq.
by rewrite seq_shift -seq_last.
Definition embed '(x, y, z) := NatNat.encode (NatNat.encode (x, y), z).
Definition unembed n := let (xy, z) := NatNat.decode n in (NatNat.decode xy, z).
Opaque embed unembed.
Definition encode_bound (x: nat): list constraint := let X n := embed (x, n, 0) in [ ((X 1) ⊍ (X 2), •0 ⊍ (h (X 1))); (* X 1 = [0..n-1], X 2 = [n] *) ((X 3) ⊍ (X 4), •0 ⊍ (h (h (X 3)))); (* X 3 = [0,2,..2*(m-1)], X 4 = [2*m] *) ((X 5) ⊍ (X 3), (X 1) ⊍ (h (X 5))); (* n = m *) ((h (X 6)) ⊍ (X 0), (X 2) ⊍ ((X 6) ⊍ ((X 6) ⊍ ((X 6) ⊍ (X 6))))); ((h (h (X 7))) ⊍ (X 0), (X 4) ⊍ ((X 7) ⊍ ((X 7) ⊍ ((X 7) ⊍ (X 7))))) (* X 0 = [0..0] of length 2^n *) ].
Definition encode_bound_spec {φ x} : mset_sat φ (encode_bound x) -> Forall (fun a => 0 = a) (φ (embed (x, 0, 0))).
Proof.
rewrite /encode_bound /mset_sat ? Forall_norm /mset_sem.
have -> (A) : map S (map S A) = map (fun i => (S 1) + i) A by rewrite map_map.
have -> : map S = map [eta Nat.add 1] by done.
move=> [/seq_spec2 [n [/eq_length Hn ->]]].
move=> [/seq_spec2 [m [/eq_length Hm ->]]].
move=> [/eq_length].
rewrite ? app_length Hn Hm ? map_length ? seq_length => ?.
have ? : n = m by lia.
subst m.
clear.
have -> : [eta Nat.add 1] = S by done.
have -> : 1 * n = n by lia.
move=> [H1 H2].
by apply: nat_spec.
Definition pyramid n := flat_map (seq 0) (seq 0 n).
Definition construct_valuation (φ: nat -> nat) (n: nat): list nat := match unembed n with | (x, 0, 0) => repeat 0 (4^(φ x)) | (x, 1, 0) => seq 0 (φ x) | (x, 2, 0) => [(φ x)] | (x, 3, 0) => map (fun i => 2*i) (seq 0 (φ x)) | (x, 4, 0) => [2*(φ x)] | (x, 5, 0) => proj1_sig (unify_sat (φ x)) | (x, 6, 0) => tower 1 (φ x) | (x, 7, 0) => tower 2 (φ x) | (x, 0, 1) => repeat 0 (φ x) | (x, 1, 1) => repeat 0 (length (pyramid (φ x))) | (x, 2, 1) => repeat 0 (4^(φ x) - (φ x)) | (x, 3, 1) => repeat 0 (4^(φ x) - (length (pyramid (φ x)))) | (x, 4, 1) => seq 0 (φ x) | (x, 5, 1) => [(φ x)] | (x, 6, 1) => pyramid (φ x) | (x, 7, 1) => flat_map pyramid (seq 0 (φ x)) | _ => [] end.
Definition encode_nat (x: nat) : list constraint := let X n := embed (x, n, 1) in [ (X 0 ⊍ X 2, mset_term_var (embed (x, 0, 0))); (* X 0 = [0..0] *) (X 1 ⊍ X 3, mset_term_var (embed (x, 0, 0))); (* X 1 = [0..0] *) (X 4 ⊍ X 5, •0 ⊍ (h (X 4))); (* X 4 = [0..m-1], X 5 = [m]*) (X 4 ⊍ X 6, X 0 ⊍ (h (X 6))); (* m = length (X 0), length (X 6) ~ m * m *) (X 6 ⊍ X 7, X 1 ⊍ (h (X 7))) (* length X 1 ~ m * m *) ].
Definition encode_constraint x y z := encode_bound x ++ encode_bound y ++ encode_bound z ++ encode_nat x ++ encode_nat y ++ encode_nat z ++ let x := embed (x, 0, 1) in let yy := embed (y, 1, 1) in let y := embed (y, 0, 1) in let z := embed (z, 0, 1) in [ (•0 ⊍ x ⊍ yy ⊍ yy ⊍ y, mset_term_var z) ].
Definition encode_h10uc '(x, y, z) := encode_constraint x y z.
End Argument.
Import H10C.
End H10UC_FMsetTC.
Module FMsetTC_FMsetC.
Import Facts mset_eq_utils mset_poly_utils.
Import H10UC_FMsetTC.
Import NatNat.
Module Argument.
Opaque NatNat.encode NatNat.decode.
Fixpoint term_to_nat (t: mset_term) : nat := match t with | mset_term_zero => 1 + NatNat.encode (0, 0) | mset_term_var x => 1 + NatNat.encode (0, 1+x) | mset_term_plus t u => 1 + NatNat.encode (1 + term_to_nat t, 1 + term_to_nat u) | mset_term_h t => 1 + NatNat.encode (1 + term_to_nat t, 0) end.
Fixpoint nat_to_term' (k: nat) (n: nat) : mset_term := match k with | 0 => mset_term_zero | S k => match n with | 0 => mset_term_zero | S n => match NatNat.decode n with | (0, 0) => mset_term_zero | (0, S x) => mset_term_var x | (S nt, 0) => mset_term_h (nat_to_term' k nt) | (S nt, S nu) => mset_term_plus (nat_to_term' k nt) (nat_to_term' k nu) end end end.
Definition nat_to_term (n: nat) : mset_term := nat_to_term' (1+n) n.
Fixpoint term_to_msetcs (t: mset_term) : list msetc := match t with | mset_term_zero => [msetc_zero (term_to_nat t)] | mset_term_var x => [] | mset_term_plus u v => [msetc_sum (term_to_nat t) (term_to_nat u) (term_to_nat v)] ++ (term_to_msetcs u) ++ (term_to_msetcs v) | mset_term_h u => [msetc_h (term_to_nat t) (term_to_nat u)] ++ (term_to_msetcs u) end.
Definition encode_eq (t u: mset_term) := [(msetc_sum 0 0 0); (msetc_sum (term_to_nat t) 0 (term_to_nat u))].
Definition encode_problem (msetcs : list constraint) : list msetc := flat_map (fun '(t, u) => (encode_eq t u) ++ term_to_msetcs t ++ term_to_msetcs u) msetcs.
End Argument.
End FMsetTC_FMsetC.
Import H10C.

Lemma encode_nat_sat_aux {n} : pyramid n ++ flat_map pyramid (seq 0 n) ≡ repeat 0 (length (pyramid n)) ++ (map S (flat_map pyramid (seq 0 n))).
Proof.
elim: n; first done.
move=> n IH.
rewrite /pyramid ? seq_last /plus ? (flat_map_concat_map, map_app, concat_app, app_length).
rewrite -?flat_map_concat_map -/pyramid -/(pyramid _) ?repeat_add seq_length /= ?app_nil_r.
apply /(eq_lr (A' := (pyramid n ++ flat_map pyramid (seq 0 n)) ++ (seq 0 n ++ pyramid n)) (B' := (repeat 0 (length (pyramid n)) ++ map S (flat_map pyramid (seq 0 n))) ++ (repeat 0 n ++ map S (pyramid n)))); [by eq_trivial | by eq_trivial |].
apply: eq_appI; first done.
by apply: pyramid_shuffle.
