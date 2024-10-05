Require Import Reals Omega mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Continuity Derive Hierarchy RInt PSeries.
Require Import Lim_seq RInt_analysis.
Section nat_to_ring.
Context {K : Ring}.
Definition nat_to_ring (n : nat) : K := sum_n_m (fun _ => one) 1 n.
End nat_to_ring.
Section is_derive_mult.
Context {K : AbsRing}.
End is_derive_mult.

Lemma is_derive_mult (f g : K -> K) x (df dg : K) : is_derive f x df -> is_derive g x dg -> (forall n m : K, mult n m = mult m n) -> is_derive (fun x : K => mult (f x) (g x)) x (plus (mult df (g x)) (mult (f x) dg)).
Proof.
intros Hf Hg Hmult.
eapply filterdiff_ext_lin.
eapply filterdiff_comp_2 => /=.
by apply Hf.
by apply Hg.
eapply filterdiff_ext_lin.
apply (filterdiff_mult (f x,g x)) => /=.
intros P [d Hd].
assert (Cf := ex_derive_continuous f x).
assert (Cg := ex_derive_continuous g x).
destruct (fun H => proj1 (filterlim_locally _ _) (Cf H) d) as [d1 Hd1].
eexists ; by apply Hf.
destruct (fun H => proj1 (filterlim_locally _ _) (Cg H) d) as [d2 Hd2].
eexists ; by apply Hg.
exists (mkposreal _ (Rmin_stable_in_posreal d1 d2)) => /= y Hy.
apply Hd ; split => /=.
eapply (Hd1 y), ball_le, Hy.
by apply Rmin_l.
eapply (Hd2 y), ball_le, Hy.
by apply Rmin_r.
by apply Hmult.
simpl => [[y1 y2]] /=.
reflexivity.
simpl => y.
rewrite /scal /=.
rewrite mult_assoc (Hmult (f x)) -!mult_assoc.
by rewrite mult_distr_l.
