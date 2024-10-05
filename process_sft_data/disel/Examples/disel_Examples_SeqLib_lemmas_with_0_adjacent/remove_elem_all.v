From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq path.
Require Import Eqdep.
Fixpoint remove_elem (xs : seq (nat * nat * seq nat)) e := match xs with | x :: xs => if x == e then xs else x :: (remove_elem xs e) | [::] => [::] end.

Lemma remove_elem_all xs p e : all p xs -> all p (remove_elem xs e).
Proof.
elim:xs=>//x xs Hi/=/andP[H1 H2].
by case B: (x==e)=>//=; rewrite H1 (Hi H2).
