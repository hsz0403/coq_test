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

Lemma incl_nth_error {X: Type} {Gamma Gamma': list X} : incl Gamma Gamma' -> exists ξ, forall x, nth_error Gamma x = nth_error Gamma' (ξ x).
Proof.
elim: Gamma Gamma'.
-
move=> Gamma' _.
exists (fun x => length Gamma').
move=> [|x] /=; apply /esym; by apply /nth_error_None.
-
move=> x Gamma IH Gamma'.
rewrite /incl -Forall_forall Forall_norm Forall_forall.
move=> [/(@In_nth_error _ _ _) [nx] Hnx /IH] [ξ Hξ].
exists (fun y => if y is S y then ξ y else nx).
by case.
