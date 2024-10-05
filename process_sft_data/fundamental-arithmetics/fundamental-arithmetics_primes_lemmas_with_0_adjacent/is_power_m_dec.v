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

Lemma is_power_m_dec : forall (n m:nat),(m>0)->{x:nat | n=(power x m)}+{p:nat & {q:nat & {r:nat & {k:nat | (is_prime p)/\(0<r)/\(r<m)/\n=(power p (q*m+r))*k/\(rel_prime p k)}}}}.
intros n m;intro H.
case (eq_nat_dec n 0);intro.
left;exists 0.
destruct m;simpl;try omega;trivial.
generalize (factorisation_exists n n0);intro.
elim H0;intro l;intro.
elim p;intros.
rewrite H2;apply wf_power_dec;trivial.
