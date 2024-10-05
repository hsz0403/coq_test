Require Import List Arith Lia Permutation.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils utils_tac utils_list utils_nat gcd rel_iter prime pos vec subcode sss.
From Undecidability.MinskyMachines.MM Require Import mm_defs mm_no_self.
From Undecidability.FRACTRAN Require Import FRACTRAN fractran_utils prime_seq.
Set Implicit Arguments.
Tactic Notation "rew" "length" := autorewrite with length_db.
Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).
Local Notation "I // s -1> t" := (mm_sss I s t).
Local Notation "P /MM/ s → t" := (sss_step (@mm_sss _) P s t) (at level 70, no associativity).
Local Notation "P /MM/ s -[ k ]-> t" := (sss_steps (@mm_sss _) P k s t) (at level 70, no associativity).
Local Notation "P /MM/ s ↓" := (sss_terminates (@mm_sss _) P s) (at level 70, no associativity).
Local Notation "l /F/ x → y" := (fractran_step l x y) (at level 70, no associativity).
Local Notation "l /F/ x -[ k ]-> y" := (fractran_steps l k x y) (at level 70, no associativity).
Set Implicit Arguments.
Definition encode_state {n} (c : nat * vec nat n) := ps (fst c) * @exp n 0 (snd c).
Definition encode_inc n i (u : pos n) := (ps (i + 1) * qs u, ps i).
Definition encode_dec n i (u : pos n) (_ : nat) := (ps (i + 1), ps i * qs u).
Definition encode_dec2 n i (u : pos n) j := (ps j, ps i).
Definition encode_one_instr m i (rho : mm_instr (pos m)) := match rho with | INC u => encode_inc i u :: nil | DEC u j => encode_dec i u j :: encode_dec2 i u j :: nil end.
Fixpoint encode_mm_instr m i (l : list (mm_instr (pos m))) : list (nat * nat) := match l with | nil => nil | rho :: l => encode_one_instr i rho ++ encode_mm_instr (S i) l end.
Fact encode_mm_instr_app m i l r : @encode_mm_instr m i (l++r) = encode_mm_instr i l++encode_mm_instr (length l+i) r.
Proof.
revert i; induction l as [ | rho l IHl ]; intros i; simpl; auto; rewrite IHl, app_ass.
do 3 f_equal; lia.
Fact encode_mm_instr_regular n i l : Forall (fun c => fst c <> 0 /\ snd c <> 0) (@encode_mm_instr n i l).
Proof.
revert i; induction l as [ | [ u | u j ] l IHl ]; intros i; simpl.
+
constructor.
+
constructor; auto; unfold encode_inc; simpl; split; [ apply Nat.neq_mul_0; split | ]; apply prime_neq_0; apply nthprime_prime.
+
constructor; [ | constructor ]; auto; split; unfold encode_dec, encode_dec2; simpl.
2: apply Nat.neq_mul_0; split.
all: apply prime_neq_0; apply nthprime_prime.
Fact encode_mm_instr_regular' n i l : fractran_regular (@encode_mm_instr n i l).
Proof.
generalize (@encode_mm_instr_regular n i l); apply Forall_impl; tauto.
Fact encode_mm_instr_in_inv n i P el c er : @encode_mm_instr n i P = el++c::er -> exists l rho r, P = l++rho::r /\ In c (encode_one_instr (length l+i) rho).
Proof.
revert i el c er; induction P as [ | rho P IHP ]; simpl; intros i el c er H.
+
destruct el; discriminate.
+
destruct list_app_cons_eq_inv with (1 := H) as [ (m & H1 & H2) | (m & H1 & H2) ].
*
destruct IHP with (1 := H2) as (l & rho' & r & G1 & G2).
exists (rho::l), rho', r; subst; split; auto.
eq goal G2; do 2 f_equal; simpl; lia.
*
exists nil, rho, P; split; simpl; auto.
rewrite <- H1; apply in_or_app; simpl; auto.
Local Notation divides_mult_inv := prime_div_mult.
Local Ltac inv H := inversion H; subst; clear H.
Opaque ps qs.
Local Fact divides_from_eq x y t : x*y = t -> divides x t.
Proof.
exists y; subst; ring.
Local Fact prime_div_mult3 p x y z : prime p -> divides p (x*y*z) -> divides p x \/ divides p y \/ divides p z.
Proof.
intros H1 H2.
apply prime_div_mult in H2; auto.
destruct H2 as [ H2 | ]; auto.
apply prime_div_mult in H2; tauto.
Local Fact prime_div_mult4 p w x y z : prime p -> divides p (w*x*y*z) -> divides p w \/ divides p x \/ divides p y \/ divides p z.
Proof.
intros H1 H2.
apply prime_div_mult3 in H2; auto.
destruct H2 as [ H2 | H2 ]; try tauto.
apply prime_div_mult in H2; tauto.
Local Hint Resolve encode_mm_instr_regular' : core.

Lemma one_step_backward m i P i1 v1 st : @mm_no_self_loops m (i, P) -> encode_mm_instr i P /F/ @encode_state m (i1,v1) → st -> exists i2 v2, st = @encode_state m (i2,v2) /\ (i, P) /MM/ (i1, v1) → (i2,v2).
Proof.
intros H1 H2.
destruct fractran_step_inv with (1 := H2) as (el & p & q & er & H3 & H4 & H5).
unfold encode_state in H5; simpl in H5.
destruct encode_mm_instr_in_inv with (1 := H3) as (l & rho & r & -> & G2).
assert (i1 = length l+i) as E.
{
unfold encode_one_instr in G2.
destruct rho as [ u | u j ]; unfold encode_inc, encode_dec, encode_dec2 in G2; [ destruct G2 as [ G2 | [] ] | destruct G2 as [ G2 | [ G2 | [] ] ] ]; inversion G2; subst p q; clear G2; repeat rewrite mult_assoc in H5.
*
apply divides_from_eq, prime_div_mult4 in H5; auto.
destruct H5 as [ H5 | [ H5 | [ H5 | H5 ] ] ].
+
apply primestream_divides in H5; lia.
+
apply ps_qs_div in H5; tauto.
+
apply primestream_divides in H5; lia.
+
apply ps_exp in H5; tauto.
*
rewrite <- mult_assoc in H5.
apply divides_from_eq, prime_div_mult3 in H5; auto.
destruct H5 as [ H5 | [ H5 | H5 ] ].
+
apply primestream_divides in H5; lia.
+
apply primestream_divides in H5; lia.
+
apply ps_exp in H5; tauto.
*
apply divides_from_eq, prime_div_mult3 in H5; auto.
destruct H5 as [ H5 | [ H5 | H5 ] ].
+
apply primestream_divides in H5.
exfalso; apply (H1 j u); auto.
+
apply primestream_divides in H5; lia.
+
apply ps_exp in H5; tauto.
}
destruct mm_sss_total with (ii := rho) (s := (i1,v1)) as ((i2 & v2) & H7).
exists i2, v2.
assert ((i, l++rho::r) /MM/ (i1,v1) → (i2,v2)) as H8.
{
apply in_sss_step; auto; simpl; lia.
}
split; auto.
apply one_step_forward in H8; auto.
revert H2 H8; apply fractran_step_fun; auto.
