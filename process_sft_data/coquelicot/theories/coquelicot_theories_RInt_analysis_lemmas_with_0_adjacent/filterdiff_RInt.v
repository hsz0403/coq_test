Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Require Import Markov Rcomplements Rbar Lub Lim_seq Derive SF_seq.
Require Import Continuity Hierarchy Seq_fct RInt PSeries.
Section Continuity.
Context {V : NormedModule R_AbsRing}.
End Continuity.
Section Derive.
Context {V : NormedModule R_AbsRing}.
End Derive.
Section Derive'.
Context {V : CompleteNormedModule R_AbsRing}.
End Derive'.
Section Comp.
Context {V : CompleteNormedModule R_AbsRing}.
End Comp.
Section RInt_comp.
Context {V : NormedModule R_AbsRing}.
End RInt_comp.
Definition PS_Int (a : nat -> R) (n : nat) : R := match n with | O => 0 | S n => a n / INR (S n) end.
Section ByParts.
Context {V : CompleteNormedModule R_AbsRing}.
End ByParts.

Lemma filterdiff_RInt (f : R -> V) (If : R -> R -> V) (a b : R) : locally (a,b) (fun u : R * R => is_RInt f (fst u) (snd u) (If (fst u) (snd u))) -> continuous f a -> continuous f b -> filterdiff (fun u : R * R => If (fst u) (snd u)) (locally (a,b)) (fun u : R * R => minus (scal (snd u) (f b)) (scal (fst u) (f a))).
Proof.
intros Hf Cfa Cfb.
assert (Ha : locally a (fun a : R => is_RInt f a b (If a b))).
case: Hf => /= e He.
exists e => x Hx.
apply (He (x,b)).
split => //.
by apply ball_center.
assert (Hb : locally b (fun b : R => is_RInt f a b (If a b))).
case: Hf => /= e He.
exists e => x Hx.
apply (He (a,x)).
split => //.
by apply ball_center.
eapply filterdiff_ext_lin.
apply (filterdiff_ext_loc (FF := @filter_filter _ _ (locally_filter _)) (fun u : R * R => plus (If (fst u) b) (minus (If a (snd u)) (If a b)))) ; last first.
apply filterdiff_plus_fct.
apply (filterdiff_comp' (fun u : R * R => fst u) (fun a : R => If a b)).
by apply filterdiff_linear, is_linear_fst.
eapply is_derive_RInt', Cfa.
by apply Ha.
apply filterdiff_plus_fct.
apply (filterdiff_comp' (fun u : R * R => snd u) (fun b : R => If a b)).
by apply filterdiff_linear, is_linear_snd.
eapply is_derive_RInt, Cfb.
by apply Hb.
apply filterdiff_const.
move => /= x Hx.
apply @is_filter_lim_locally_unique in Hx.
by rewrite -Hx /= minus_eq_zero plus_zero_r.
simpl.
have : (locally (a,b) (fun u : R * R => is_RInt f (fst u) b (If (fst u) b))) => [ | {Ha} Ha].
case: Ha => /= e He.
exists e => y Hy.
apply He, Hy.
have : (locally (a,b) (fun u : R * R => is_RInt f a (snd u) (If a (snd u)))) => [ | {Hb} Hb].
case: Hb => /= e He.
exists e => y Hy.
apply He, Hy.
move: (locally_singleton _ _ Hf) => /= Hab.
generalize (filter_and _ _ Hf (filter_and _ _ Ha Hb)).
apply filter_imp => {Hf Ha Hb} /= u [Hf [Ha Hb]].
apply sym_eq, (filterlim_locally_unique _ _ _ Hf).
apply is_RInt_Chasles with b => //.
rewrite /minus plus_comm.
apply is_RInt_Chasles with a => //.
by apply is_RInt_swap.
simpl => y.
rewrite scal_opp_r plus_zero_r.
apply plus_comm.
