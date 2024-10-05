Require Import missing.
Require Import division.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition quotient_euclide (a b:nat)(H:(b<>O)) := let (q,_) := (euclide a b H) in q.
Definition remainder_euclide (a b:nat)(H:(b<>O)) := let (_,e0) := (euclide a b H) in let (r,_) := e0 in r.

Lemma divides_nat : forall (n:nat),{p:nat | (p<>1)/\(p<>n)/\(divides n p)}+{forall (p:nat),(p<>1)->(p<>n)->~(divides n p)}.
intros.
case (dec_impl_lt_dec (fun p => (p<>1)/\(divides n p))) with n;intros.
case (divides_dec n n0);intro.
case (eq_nat_dec n0 1);intros.
right;intro;tauto.
left;tauto.
right;tauto.
elim s;intros.
left;exists x.
split;try tauto.
split;try tauto.
omega.
case (eq_nat_dec n 0);intro.
rewrite e;left;exists 2.
split;try (intro;discriminate).
split;try (intro;discriminate).
apply zero_max_div.
right;intros.
case (lt_eq_lt_dec p n);intro.
case s;intro;[red in n0;intro;apply n0 with p;tauto | auto].
intro;generalize (divides_le n p n1 H1);omega.
