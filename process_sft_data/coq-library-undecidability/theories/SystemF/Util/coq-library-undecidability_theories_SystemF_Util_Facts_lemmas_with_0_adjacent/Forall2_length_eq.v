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

Lemma Forall2_length_eq {X Y: Type} {R: X -> Y -> Prop} {l1 l2} : Forall2 R l1 l2 -> length l1 = length l2.
Proof.
elim: l1 l2.
-
move=> [| ? ?] H; first done.
by inversion H.
-
move=> ? ? IH [| ? ?] /= H; inversion H.
congr S.
by apply: IH.
