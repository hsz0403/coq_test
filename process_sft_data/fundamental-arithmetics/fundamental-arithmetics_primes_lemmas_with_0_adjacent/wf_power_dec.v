Require Import missing.
Require Import division.
Require Import euclide.
Require Import gcd.
Require Import power.
Require Import permutation.
Require Import Wf_nat.
Unset Standard Proposition Elimination Names.
Definition is_prime (p:nat) := (p<>1)/\(forall (d:nat),(divides p d)->(d=1)\/(d=p)).
Fixpoint refactor (l:(list (nat*nat))) {struct l} : nat := match l with nil => 1 | (cons (p,n) tail) => (power p n)*(refactor tail) end.
Inductive is_wf : (list (nat*nat))->Prop := nil_is_wf : (is_wf nil) |cons_is_wf : forall (p n:nat)(tail:(list (nat*nat))),(is_prime p)->(n>0)->(is_wf tail)->(rel_prime p (refactor tail))->(is_wf (cons (p,n) tail)).
Inductive is_pwd : list (nat*nat) -> Prop := nil_is_pwd : (is_pwd nil) |cons_is_pwd : forall (p n:nat)(tail:list (nat*nat)),(is_pwd tail)->(forall (n:nat),~(In (p,n) tail))->(is_pwd ((p,n)::tail)).
Definition is_factorisation (n:nat)(l:list (nat*nat)) := (is_wf l)/\(n=(refactor l)).

Lemma wf_power_dec : forall (n:nat)(l:list (nat*nat)),(is_wf l)->(n>0)->{x:nat | (refactor l)=(power x n)}+{p:nat & {q:nat & {r:nat & {k:nat | (is_prime p)/\(0<r)/\(r<n)/\(refactor l)=(power p (q*n+r))*k/\(rel_prime p k)}}}}.
intro.
induction l;simpl;intros.
left;exists 1;rewrite power_one;trivial.
destruct a.
assert (n<>0);try omega.
generalize (quo_rem_euclide n1 n H1);intro.
case (eq_nat_dec (remainder_euclide n1 n H1) 0);intro.
rewrite e in H2;rewrite plus_comm in H2;simpl in H2.
case IHl;intros;trivial.
inversion H;trivial.
elim s;intro y;intro.
rewrite H2.
left;rewrite p;rewrite (mult_comm n);rewrite <- power_power_lemma1;rewrite <- power_mult_lemma1;exists (power n0 (quotient_euclide n1 n H1)*y);trivial.
elim s;intro p;intro.
elim p0;intro q;intro.
elim p1;intro r;intro.
elim p2;intro k;intro.
elim p3;intros.
elim H4;intros.
elim H6;intros.
elim H8;intros.
right.
exists p;exists q;exists r.
rewrite H9;rewrite mult_comm;rewrite <- mult_assoc.
exists (k*(power n0 n1)).
split;trivial.
split;trivial.
split;trivial.
split;trivial.
apply rel_prime_mult;trivial.
inversion H.
rewrite H9 in H17.
elim (mult_rel_prime n0 (power p (q*n+r)) k H17);intros.
apply rel_prime_power;apply rel_prime_sym;apply power_rel_prime with (q*n+r);trivial.
rewrite plus_comm;auto with arith.
right.
exists n0;exists (quotient_euclide n1 n H1);exists (remainder_euclide n1 n H1).
rewrite (mult_comm (quotient_euclide n1 n H1));rewrite <- H2.
exists (refactor l).
elim (in_wf ((n0,n1)::l) n0 n1);intros.
split;trivial.
split;trivial.
destruct (remainder_euclide n1 n H1);try tauto;auto with arith.
split;trivial.
apply rem_euclide.
split;trivial.
inversion H;trivial.
simpl;tauto.
trivial.
