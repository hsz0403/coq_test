From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Computability Require Import Enum.
From Undecidability.L.Functions Require Import Encoding Equality.
From Undecidability.L.Datatypes Require Import LNat Lists LProd.
Require Import Undecidability.Shared.Libs.PSL.Base Nat List Datatypes.
Set Default Proof Using "Type".
Import Nat.
Instance term_appCross : computableTime' appCross (fun A _ => (5,fun B _ => (length A * length B * 29 + length A * 46 + 4,tt))).
Proof.
extract.
solverec.
fold appCross;rewrite map_time_const,map_length.
unfold c__map, c__app.
Lia.nia.
Instance term_exh_size : computable exh_size.
Proof.
extract.
Definition T_nondec_helper A x : bool := negb (inb term_eqb x A) .
Fixpoint T_nondec (n : nat) : list term := match n with | 0 => [# n] | S n0 => T_nondec n0 ++ [# (S n0)] ++ filter (T_nondec_helper (T_nondec n0)) (map lam (T_nondec n0) ++ appCross (T_nondec n0) (T_nondec n0)) end.
Local Instance term_T_nondec : computable T_nondec.
Proof.
assert (computable T_nondec_helper).
extract.
extract.
Instance term_T : computable T.
Proof.
eapply computableExt with (x:= T_nondec).
2:exact _.
repeat intro.
symmetry.
apply T_nondec_correct.
Instance term_g_inv : computable g_inv.
Proof.
unfold g_inv.
extract.
Definition g_nondec s := match pos_nondec term_eqb s (T (exh_size s)) with | Some n => n | None => 0 end.
Local Instance term_g_nondec : computable g_nondec.
Proof.
unfold g_nondec.
extract.
Instance term_g : computable g.
Proof.
eapply computableExt with (x:= g_nondec).
2:exact _.
repeat intro.
symmetry.
apply g_nondec_correct.
Local Definition f_filter A x := negb (inb (prod_eqb Nat.eqb Nat.eqb) x A).
Local Definition f_map (p : nat * nat) := let (p1, p2) := p in (p1, S p2).
Fixpoint C_nondec (n : nat) : list (nat * nat) := match n with | 0 => [(0, 0)] | S n0 => let C' := C_nondec n0 in C' ++ (S n0, 0) :: filter (f_filter C') (map f_map C') end.
Local Instance term_C_nondec : computable C_nondec.
Proof.
assert (computable f_filter) by extract.
assert (computable f_map) by extract.
extract.
Instance term_C : computable C.
Proof.
eapply computableExt with (x:= C_nondec).
2:exact _.
repeat intro.
symmetry.
apply C_nondec_correct.
Instance term_eSize : computable eSize.
Proof.
extract.
Instance term_c : computable c.
Proof.
extract.

Instance term_g_inv : computable g_inv.
Proof.
unfold g_inv.
extract.
