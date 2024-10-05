Require Import List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Fact copy {A : Type} : A -> A * A.
Proof.
done.
Fact iter_last {X: Type} {f: X -> X} {n x} : Nat.iter n f (f x) = Nat.iter (1+n) f x.
Proof.
elim: n x; [done | by move=> n /= + x => ->].
Arguments measure_ind {X}.
Section ForallNorm.
Variable T : Type.
Variable P : T -> Prop.
Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).
End ForallNorm.

Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof.
Admitted.

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : Nat.iter n f (Nat.iter m f x) = Nat.iter (n + m) f x.
Proof.
Admitted.

Fact iter_last {X: Type} {f: X -> X} {n x} : Nat.iter n f (f x) = Nat.iter (1+n) f x.
Proof.
Admitted.

Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
apply : well_founded_ind.
apply : Wf_nat.well_founded_lt_compat.
move => *.
Admitted.

Lemma Forall_nilP : Forall P [] <-> True.
Proof.
Admitted.

Lemma Forall_consP {a A} : Forall P (a :: A) <-> P a /\ Forall P A.
Proof.
Admitted.

Lemma Forall_singletonP {a} : Forall P [a] <-> P a.
Proof.
rewrite Forall_consP Forall_nilP.
Admitted.

Lemma Forall_appP {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
elim: A; first by (constructor; by [|case]).
move=> ? ? IH /=.
Admitted.

Lemma Forall_appI {A B}: Forall P A -> Forall P B -> Forall P (A ++ B).
Proof.
move=> ? ?.
apply /Forall_appP.
Admitted.

Lemma nth_error_map {X Y: Type} {f: X -> Y} {l: list X} {n: nat} : nth_error (map f l) n = omap f (nth_error l n).
Proof.
elim: n l; first by case.
move=> n IH.
case; first done.
move=> x l /=.
Admitted.

Fact copy {A : Type} : A -> A * A.
Proof.
done.
