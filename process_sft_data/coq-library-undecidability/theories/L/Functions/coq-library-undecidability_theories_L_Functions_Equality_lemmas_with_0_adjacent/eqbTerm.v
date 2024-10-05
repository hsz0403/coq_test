From Undecidability.L Require Export Datatypes.LBool Datatypes.LNat Datatypes.LTerm.
Require Import Nat.
From Undecidability.L Require Import Tactics.LTactics Functions.EqBool.
Import EqBool.
Fixpoint term_eqb s t := match s,t with | var n, var m => eqb n m | L.app s1 t1, L.app s2 t2 => andb (term_eqb s1 s2) (term_eqb t1 t2) | lam s',lam t' => term_eqb s' t' | _,_ => false end.
Instance eqbTerm : eqbClass term_eqb.
Proof.
exact term_eqb_spec.
Instance eqbComp_nat : eqbCompT term.
Proof.
evar (c:nat).
exists c.
unfold term_eqb.
unfold enc;cbn.
unfold term_enc.
extract.
unfold eqb,eqbTime.
[c]:exact (5 + c__eqbComp nat).
all:unfold c.
set (c__eqbComp nat).
change (LNat.nat_enc) with (enc (X:=nat)).
solverec.
all:try nia.

Instance eqbTerm : eqbClass term_eqb.
Proof.
exact term_eqb_spec.
