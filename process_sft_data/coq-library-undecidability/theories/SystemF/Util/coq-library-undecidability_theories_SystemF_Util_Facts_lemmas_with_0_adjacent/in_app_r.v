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

Lemma in_app_r {X: Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof.
move=> ?.
apply /in_app_iff.
by right.
