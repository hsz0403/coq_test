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

Lemma square_spec {n A} : (seq 0 n) ++ A ≡ (repeat 0 n) ++ (map S A) -> length A + length A + n = n * n.
Proof.
elim: n A.
{
move=> A /eq_symm /eq_mapE ->; [by lia | done].
}
move=> n IH A.
rewrite seq_last /(plus 0 _).
move /(eq_lr _ eq_refl (A' := seq 0 n ++ (n :: A))) => /(_ ltac:(by eq_trivial)).
move /square_spec_aux => [A' [/eq_length + /IH]].
rewrite app_length seq_length.
Admitted.

Lemma encode_nat_spec {φ x} : mset_sat φ (encode_bound x) -> mset_sat φ (encode_nat x) -> length (φ (embed (x, 1, 1))) + length (φ (embed (x, 1, 1))) + length (φ (embed (x, 0, 1))) = length (φ (embed (x, 0, 1))) * length (φ (embed (x, 0, 1))).
Proof.
move /encode_bound_spec.
rewrite /mset_sat /encode_nat ?Forall_norm /mset_sem.
pose X n := φ (embed (x, n, 1)).
rewrite -?/(X _).
move=> H [/eq_Forall_iff /(_ [eta eq 0]) /iffRL /(_ H)].
rewrite Forall_norm=> [[HX0 _]].
move=> [/eq_Forall_iff /(_ [eta eq 0]) /iffRL /(_ H)].
rewrite Forall_norm=> [[? _]].
have -> : map S (X 4) = map [eta Init.Nat.add 1] (X 4) by done.
move=> [/seq_spec2 [n]].
have -> : map [eta Init.Nat.mul 1] (seq 0 n) = map id (seq 0 n).
{
under map_ext => i do have -> : 1*i = i by lia.
done.
}
rewrite map_id => [[Hn _]].
move=> [/eq_symm /eq_trans] => /(_ ((seq 0 n) ++ X 6)).
apply: unnest; first by apply: eq_appI.
move=> HX6.
have HlX0 : length (X 0) = n.
{
move: HX6 => /eq_length.
rewrite ? app_length map_length seq_length.
by lia.
}
move: HX6 => /eq_symm.
have -> := Forall_repeat HX0.
rewrite HlX0.
move /square_spec => ? /eq_length.
rewrite ?app_length map_length repeat_length.
Admitted.

Lemma pyramid_shuffle {n} : seq 0 n ++ pyramid n ≡ repeat 0 n ++ map S (pyramid n).
Proof.
elim: n; first done.
move=> n IH.
rewrite /pyramid seq_last /plus flat_map_concat_map map_app concat_app.
rewrite -flat_map_concat_map -/(pyramid _) ? map_app /= ? app_nil_r seq_shift.
apply /(eq_lr (A' := (seq 0 n ++ [n]) ++ (seq 0 n ++ pyramid n)) (B' := (0 :: seq 1 n) ++ (repeat 0 n ++ map S (pyramid n)))); [ by eq_trivial | by eq_trivial | ].
rewrite -seq_last -/(seq _ (S n)).
Admitted.

Lemma pyramid_length n : n + length (pyramid n) <= 4 ^ n.
Proof.
elim: n; first by (move=> /=; lia).
move=> n IH.
rewrite /pyramid seq_last /plus -/plus flat_map_concat_map map_app concat_app app_length.
rewrite -flat_map_concat_map -/(pyramid _).
rewrite /map /concat app_length seq_length /=.
have := Nat.pow_gt_lin_r 4 n ltac:(lia).
Admitted.

Lemma encode_nat_sat_aux {n} : pyramid n ++ flat_map pyramid (seq 0 n) ≡ repeat 0 (length (pyramid n)) ++ (map S (flat_map pyramid (seq 0 n))).
Proof.
elim: n; first done.
move=> n IH.
rewrite /pyramid ? seq_last /plus ? (flat_map_concat_map, map_app, concat_app, app_length).
rewrite -?flat_map_concat_map -/pyramid -/(pyramid _) ?repeat_add seq_length /= ?app_nil_r.
apply /(eq_lr (A' := (pyramid n ++ flat_map pyramid (seq 0 n)) ++ (seq 0 n ++ pyramid n)) (B' := (repeat 0 (length (pyramid n)) ++ map S (flat_map pyramid (seq 0 n))) ++ (repeat 0 n ++ map S (pyramid n)))); [by eq_trivial | by eq_trivial |].
apply: eq_appI; first done.
Admitted.

Lemma encode_nat_sat {φ x} : mset_sat (construct_valuation φ) (encode_nat x).
Proof.
rewrite /encode_nat /mset_sat ?Forall_norm /mset_sem /construct_valuation ?embed_unembed.
rewrite -?repeat_add.
constructor.
{
apply: eq_eq.
f_equal.
have := pyramid_length (φ x).
by lia.
}
constructor.
{
apply: eq_eq.
f_equal.
have := pyramid_length (φ x).
by lia.
}
constructor; first by apply: seq_sat1.
constructor; first by apply: pyramid_shuffle.
Admitted.

Lemma encode_constraint_spec {φ x y z} : mset_sat φ (encode_constraint x y z) -> 1 + length (φ (embed (x, 0, 1))) + length(φ (embed (y, 0, 1))) * length(φ (embed (y, 0, 1))) = length(φ (embed (z, 0, 1))).
Proof.
rewrite /encode_constraint /mset_sat ?Forall_app_iff -?/(mset_sat _ _).
move=> [Hx [Hy [Hz]]].
move=> [/(encode_nat_spec Hx) ? [/(encode_nat_spec Hy) ? [/(encode_nat_spec Hz) ?]]].
rewrite /mset_sat Forall_norm /mset_sem.
move /eq_length.
rewrite ? app_length /=.
Admitted.

Lemma encode_constraint_sat {φ x y z} : 1 + (φ x) + (φ y) * (φ y) = (φ z) -> mset_sat (construct_valuation φ) (encode_constraint x y z).
Proof.
move=> Hxyz.
rewrite /encode_constraint /mset_sat ? Forall_app_iff Forall_singleton_iff -?/(mset_sat _ _).
do 3 (constructor; first by apply: encode_bound_sat).
do 3 (constructor; first by apply: encode_nat_sat).
rewrite /mset_sem /construct_valuation ? embed_unembed.
have ->: [0] = repeat 0 1 by done.
rewrite -?repeat_add.
apply: eq_eq.
f_equal.
move: Hxyz=> <-.
clear.
elim: (φ y); clear; first by (move=> /=; lia).
move=> φy IH.
rewrite /pyramid seq_last /(plus 0 _) flat_map_concat_map map_app concat_app.
rewrite -flat_map_concat_map -/(pyramid _) /= ?app_length seq_length /=.
Admitted.

Theorem reduction : H10UC_SAT ⪯ FMsetTC_SAT.
Proof.
exists (fun h10ucs => flat_map Argument.encode_h10uc h10ucs).
move=> h10ucs.
constructor.
-
move=> [φ Hφ].
exists (Argument.construct_valuation φ).
elim: h10ucs Hφ; first by constructor.
move=> [[x y] z] h10cs IH.
move /Forall_forall.
rewrite Forall_cons_iff.
move=> [Hxyz /Forall_forall /IH].
move=> {}IH.
apply /Forall_app_iff.
constructor; last done.
by apply: Argument.encode_constraint_sat.
-
move=> [φ] Hφ.
pose ψ := (fun x => length (φ (Argument.embed (x, 0, 1)))).
exists ψ.
rewrite -Forall_forall.
elim: h10ucs Hφ; first done.
move=> [[x y] z] h10ucs IH.
rewrite /flat_map -/(flat_map _) /mset_sat Forall_app_iff /(Argument.encode_h10uc _).
move=> [/Argument.encode_constraint_spec Hxyz /IH ?].
Admitted.

Lemma nat_term_cancel {t} : nat_to_term (term_to_nat t) = t.
Proof.
rewrite /nat_to_term.
move Hk: (k in nat_to_term' k _) => k.
have : term_to_nat t < k by lia.
elim: t k {Hk}.
-
move=> [|k]; [by lia | done].
-
move=> x [|k]; first by lia.
by rewrite /= NatNat.decode_encode.
-
move=> nt IHt nu IHu [|k]; first by lia.
rewrite /= NatNat.decode_encode => ?.
have ? := NatNat.encode_non_decreasing (S (term_to_nat nt)) (S (term_to_nat nu)).
rewrite IHt; first by lia.
by rewrite IHu; first by lia.
-
move=> nt IH [|k]; first by lia.
rewrite /= NatNat.decode_encode => ?.
have ? := NatNat.encode_non_decreasing (S (term_to_nat nt)) 0.
Admitted.

Lemma completeness {l} : FMsetTC_SAT l -> FMsetC_SAT (encode_problem l).
Proof.
move=> [φ] Hφ.
pose ψ x := if x is 0 then [] else mset_sem φ (nat_to_term x).
have Hψ (A) : Forall (msetc_sem ψ) (term_to_msetcs A).
{
elim: A.
-
by rewrite /term_to_msetcs ? Forall_norm /ψ.
-
by rewrite /term_to_msetcs.
-
move=> A IHA B IHB.
rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
constructor; last by constructor.
rewrite /ψ /msetc_sem ? nat_term_cancel.
by rewrite ? term_to_nat_pos.
-
move=> A IH.
rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
constructor; last done.
rewrite /ψ /msetc_sem ? nat_term_cancel.
by rewrite ? term_to_nat_pos.
}
exists ψ.
rewrite - Forall_forall /encode_problem Forall_flat_mapP.
apply: Forall_impl; last eassumption.
move=> [A B].
rewrite ? Forall_norm.
move=> HφAB.
constructor; last by constructor.
constructor; first done.
rewrite /ψ /msetc_sem.
rewrite (@term_to_nat_pos A) (@term_to_nat_pos B).
Admitted.

Lemma soundness {l} : FMsetC_SAT (encode_problem l) -> FMsetTC_SAT l.
Proof.
move=> [ψ].
rewrite -Forall_forall Forall_flat_mapP => Hψ.
pose φ x := ψ (term_to_nat (mset_term_var x)).
exists φ.
apply: Forall_impl; last by eassumption.
move=> [t u].
rewrite ? Forall_norm => [[+ [+]]].
rewrite /msetc_sem -/(msetc_sem _).
move=> [/eq_app_nil_nilP /copy [Hψ0 ->]].
rewrite /app => Hψtu.
have Hφ (s) : Forall (msetc_sem ψ) (term_to_msetcs s) -> mset_sem φ s ≡ (ψ (term_to_nat s)).
{
clear.
elim: s.
-
rewrite /term_to_msetcs ? Forall_norm /msetc_sem /φ /mset_sem.
by apply /eq_symm.
-
by move=> x _.
-
move=> t IHt u IHu.
rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
move=> [+ [/IHt {}IHt /IHu {}IHu]].
rewrite /msetc_sem /φ /mset_sem -/mset_sem -/φ.
move /eq_symm.
apply /eq_trans.
by apply: eq_appI.
-
move=> t IH.
rewrite /term_to_msetcs -/term_to_msetcs ? Forall_norm.
move=> [+ /IH {}IH].
rewrite /msetc_sem /φ /mset_sem -/mset_sem -/φ.
move /eq_symm.
apply /eq_trans.
by apply: eq_mapI.
}
move=> /Hφ Ht /Hφ Hu.
Admitted.

Theorem reduction : FMsetTC_SAT ⪯ FMsetC_SAT.
Proof.
exists Argument.encode_problem.
move=> cs.
constructor.
-
exact Argument.completeness.
-
Admitted.

Theorem reduction : H10UC_SAT ⪯ FMsetC_SAT.
Proof.
eapply reduces_transitive.
-
exact H10UC_FMsetTC.reduction.
-
Admitted.

Lemma term_to_nat_pos {t} : term_to_nat t = S (Nat.pred (term_to_nat t)).
Proof.
case: t; by move=> *.
