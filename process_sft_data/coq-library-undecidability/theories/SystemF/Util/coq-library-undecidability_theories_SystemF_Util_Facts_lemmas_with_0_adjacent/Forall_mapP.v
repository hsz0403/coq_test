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

Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
elim: l.
-
move=> /=.
by constructor.
-
move=> a l IH /=.
by rewrite ? Forall_norm IH.
