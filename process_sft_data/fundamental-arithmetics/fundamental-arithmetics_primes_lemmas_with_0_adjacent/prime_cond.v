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

Lemma prime_cond : forall (p:nat),((p<>1)/\(forall (a:nat),(a<>1)->(a<>p)->~(divides p a))<->(is_prime p)).
split;intros.
elim H;intros.
split;try tauto.
intros.
case (eq_nat_dec d 1);intro;try tauto.
case (eq_nat_dec d p);intro;try tauto.
elim (H1 d n n0 H2).
elim H;intros.
split;try tauto.
intros;intro.
elim (H1 a H4);auto.
