Require Import SetoidList.
Require OrderedType.
Require Import Orders.
Instance not_symmetric (A : Type) (R: relation A) `{Symmetric A R} : Symmetric (fun x y => ~R x y).
Proof.
intros ? ? Hnot HR.
apply Hnot.
symmetry.
assumption.
Instance InA_compat {A : Type} : Proper (subrelation ==> eq ==> eq ==> impl) (@InA A).
Proof.
intros inA inB Hin.
do 6 intro; subst.
intro Hl.
rewrite InA_alt in *.
destruct Hl as [? [? ?]].
eexists.
split; eauto.
Definition full_relation {A : Type} : relation A := fun x y : A => True.
Module OTconvert (O : OrderedType) : OrderedType.OrderedType with Definition t := O.t with Definition eq := O.eq with Definition lt := O.lt.
Definition t := O.t.
Definition eq := O.eq.
Definition lt := O.lt.
Definition eq_refl : forall x, eq x x := reflexivity.
Definition eq_dec := O.eq_dec.
End OTconvert.

Instance not_symmetric (A : Type) (R: relation A) `{Symmetric A R} : Symmetric (fun x y => ~R x y).
Proof.
intros ? ? Hnot HR.
apply Hnot.
symmetry.
assumption.
