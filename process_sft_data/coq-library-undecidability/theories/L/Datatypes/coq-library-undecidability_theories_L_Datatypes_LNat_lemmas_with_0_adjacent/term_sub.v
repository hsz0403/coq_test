From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Export LTactics GenEncode.
Require Import Undecidability.Shared.Libs.PSL.Numbers.
Require Import Nat.
From Undecidability.L Require Import Datatypes.LBool Functions.EqBool Datatypes.LProd.
Import GenEncode.
Import Nat.
MetaCoq Run (tmGenEncode "nat_enc" nat).
Hint Resolve nat_enc_correct : Lrewrite.
Instance termT_S : computableTime' S (fun _ _ => (1,tt)).
Proof.
extract constructor.
solverec.
Instance termT_pred : computableTime' pred (fun _ _ => (5,tt)).
Proof.
extract.
solverec.
Definition c__add := 11.
Definition c__add1 := 5.
Definition add_time x := (x + 1) * c__add.
Instance termT_plus' : computableTime' add (fun x xT => (c__add1,(fun y yT => (add_time x,tt)))).
Proof.
extract.
fold add.
solverec.
all: unfold add_time, c__add1, c__add; solverec.
Definition c__mult1 := 5.
Definition c__mult := c__add + c__add1 + 10.
Definition mult_time x y := x * y * c__mult + c__mult * (x+ 1) .
Instance termT_mult : computableTime' mult (fun x xT => (c__mult1,(fun y yT => (mult_time x y,tt)))).
Proof.
extract.
solverec.
all: unfold mult_time, c__mult1, c__mult, add_time, c__add1, c__add; solverec.
Definition c__sub1 := 5.
Definition c__sub := 14.
Definition sub_time x y := (min x y + 1) * c__sub.
Instance term_sub : computableTime' Nat.sub (fun n _ => (c__sub1,fun m _ => (sub_time n m ,tt)) ).
Proof.
extract.
solverec.
all: unfold sub_time, c__sub1, c__sub; solverec.
Definition c__leb := 14.
Definition c__leb2 := 5.
Definition leb_time (x y : nat) := c__leb * (1 + min x y).
Instance termT_leb : computableTime' leb (fun x xT => (c__leb2,(fun y yT => (leb_time x y,tt)))).
Proof.
extract.
solverec.
all: unfold leb_time, c__leb, c__leb2; solverec.
Definition c__ltb := c__leb2 + 4.
Definition ltb_time (a b : nat) := leb_time (S a) b + c__ltb.
Instance term_ltb : computableTime' Nat.ltb (fun a _ => (1, fun b _ => (ltb_time a b, tt))).
Proof.
extract.
recRel_prettify2.
-
lia.
-
unfold ltb_time, c__ltb.
solverec.
Instance eqbNat_inst : eqbClass Nat.eqb.
Proof.
exact Nat.eqb_spec.
Instance eqbComp_nat : eqbCompT nat.
Proof.
evar (c:nat).
exists c.
unfold Nat.eqb.
unfold enc;cbn.
extract.
solverec.
[c]:exact 5.
all:unfold c;try lia.
Definition c__min1 := 5.
Definition c__min2 := 15.
Definition min_time x y := (min x y + 1) * c__min2.
Instance termT_nat_min : computableTime' Nat.min (fun x _ => (c__min1, fun y _ => (min_time x y, tt))).
Proof.
extract.
solverec.
all: unfold min_time, c__min1, c__min2; solverec.
Definition c__max1 := 5.
Definition c__max2 := 15.
Definition max_time x y := (min x y + 1) * c__max2.
Instance termT_nat_max : computableTime' Nat.max (fun x _ => (c__max1, fun y _ => (max_time x y, tt))).
Proof.
extract.
solverec.
all: unfold max_time, c__max1, c__max2; solverec.
Definition c__pow1 := 5.
Definition c__pow2 := 10 + c__mult1.
Fixpoint pow_time x n := match n with | 0 => c__pow2 | S n => pow_time x n + mult_time x (x ^n) + c__pow2 end.
Instance termT_pow: computableTime' Init.Nat.pow (fun (x : nat) _ => (c__pow1,fun (n : nat) _ => (pow_time x n, tt))).
Proof.
extract.
fold Nat.pow.
solverec.
all: unfold pow_time, c__pow1, c__pow2; solverec.
Definition c__divmod := 20.
Definition divmod_time (x: nat) := c__divmod * (1+x).
Instance termT_divmod : computableTime' divmod (fun (x : nat) _ => (5, fun (y : nat) _ => (5, fun (q : nat) _ => (1, fun (u : nat) _ => (divmod_time x, tt))))).
Proof.
extract.
solverec.
all: unfold divmod_time, c__divmod; solverec.
Definition c__modulo := 21 + c__sub1.
Definition modulo_time (x :nat) (y : nat) := divmod_time x + c__sub * y + c__modulo.
Instance termT_modulo : computableTime' Init.Nat.modulo (fun x _ => (1, fun y _ => (modulo_time x y, tt))).
Proof.
extract.
solverec.
-
unfold modulo_time, c__modulo; solverec.
-
unfold sub_time.
rewrite Nat.le_min_l.
unfold modulo_time, c__modulo.
solverec.
Fixpoint nat_unenc (s : term) := match s with | lam (lam #1) => Some 0 | lam (lam (app #0 s)) => match nat_unenc s with Some n => Some (S n) | x=>x end | _ => None end.
Definition c__natsizeO := 4.
Definition c__natsizeS := 4.

Instance term_sub : computableTime' Nat.sub (fun n _ => (c__sub1,fun m _ => (sub_time n m ,tt)) ).
Proof.
extract.
solverec.
all: unfold sub_time, c__sub1, c__sub; solverec.
