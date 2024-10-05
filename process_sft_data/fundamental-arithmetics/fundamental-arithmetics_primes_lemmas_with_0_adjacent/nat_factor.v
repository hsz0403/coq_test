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

Lemma nat_factor : forall (n p:nat),(is_prime p)->(n<>0)->{m:nat | (divides n (power p m))/\~(divides n (power p (m+1)))}.
intros n p H.
apply (lt_wf_rec n (fun n:nat => n <> 0 -> {m : nat | divides n (power p m) /\ ~ divides n (power p (m + 1))}));intros.
case (divides_dec n0 p);intro.
generalize (quo_is_quo n0 p d);intro.
elim (H0 (quo n0 p d)).
intro m;intros.
exists (m+1).
elim p0;intros.
elim H3;intros.
rewrite H5 in H2;rewrite mult_assoc in H2.
rewrite plus_comm.
split;simpl.
exists x;trivial.
rewrite plus_comm;simpl.
rewrite (mult_comm p (power p m));rewrite mult_assoc;intro.
elim H6;intros.
rewrite H2 in H7.
assert (p<>0).
intro.
rewrite H8 in H.
apply not_prime_zero;trivial.
assert ((power p m)*x=(power p m)*p*x0).
apply mult_lemma6 with p;trivial.
rewrite mult_assoc;rewrite H7;ring.
rewrite <- H5 in H9;rewrite (mult_comm (power p m) p) in H9.
apply H4.
rewrite plus_comm;simpl.
exists x0;trivial.
rewrite mult_comm in H2;rewrite H2;apply mult_lemma3.
intro.
apply H1;rewrite H2;rewrite H3;trivial.
elim H.
intros.
destruct p;omega.
intro;apply H1.
rewrite H2;rewrite H3;ring.
exists 0;simpl.
split.
apply one_min_div.
rewrite mult_comm;simpl;rewrite plus_comm;simpl;trivial.
