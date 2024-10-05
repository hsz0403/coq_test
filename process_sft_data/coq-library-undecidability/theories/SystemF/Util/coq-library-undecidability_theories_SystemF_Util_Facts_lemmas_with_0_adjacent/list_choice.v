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

Lemma list_choice {P : nat -> nat -> Prop} {l: list nat} : Forall (fun i : nat => exists n : nat, P i n) l -> exists φ, Forall (fun i : nat => P i (φ i)) l.
Proof.
elim /rev_ind: l.
-
move=> ?.
exists id.
by constructor.
-
move=> k l IH.
rewrite Forall_app.
move=> [/IH [φ Hφ]] /(@Forall_inv _ _ _) [n Hn].
exists (fun i => if PeanoNat.Nat.eq_dec i k then n else φ i).
rewrite Forall_app.
constructor.
+
move: Hφ.
rewrite ?Forall_forall => H i.
case: (PeanoNat.Nat.eq_dec _ _); [by move=> /= -> | by move=> *; apply: H].
+
constructor; last done.
by case: (PeanoNat.Nat.eq_dec _ _).
