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

Lemma factorisation : forall (n:nat),{l:(list (nat*nat)) | (is_wf l)/\n=(refactor l)}+{n=0}.
intro.
case (eq_nat_dec n 0);intro.
right;trivial.
case (eq_nat_dec n 1).
intro;left;exists (nil (A:=nat*nat)).
split;[apply nil_is_wf | simpl;trivial].
generalize n0.
apply (lt_wf_rec n (fun n:nat => n<>0 -> n <> 1 -> {l : list (nat * nat) | is_wf l /\ n = refactor l}+{n=0}));intros.
elim (nat_factor_prime n1 H0 H1).
intro p;intro.
elim p0;intro m;intro.
elim p1;intro q;intro.
elim p2;intros.
elim H3;intros.
elim H5;intros.
elim H7;intros.
case (eq_nat_dec q 1);intro.
left;exists (cons (p,m) nil);simpl;rewrite e in H6.
split;trivial.
apply cons_is_wf;auto;try (apply nil_is_wf).
unfold rel_prime;simpl;rewrite e in H8;trivial.
assert (q<>0).
intro;rewrite H10 in H6;rewrite mult_comm in H6;simpl in H6;auto.
elim (H q H9 H10 n2).
intro.
elim a;intro l;intro.
elim p3;intros.
left;exists (cons (p,m) l);simpl;rewrite H12 in H6;split;trivial.
apply cons_is_wf;auto.
rewrite <- H12;unfold rel_prime;trivial.
intro;tauto.
