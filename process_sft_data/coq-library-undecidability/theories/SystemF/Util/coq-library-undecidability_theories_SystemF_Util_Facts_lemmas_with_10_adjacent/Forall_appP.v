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

Fact copy {A : Type} : A -> A * A.
Proof.
Admitted.

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
Admitted.

Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
elim: l.
-
move=> /=.
by constructor.
-
move=> a l IH /=.
Admitted.

Lemma Forall_seqP {P : nat -> Prop} {m n: nat} : Forall P (seq m n) <-> (forall i, m <= i < m + n -> P i).
Proof.
rewrite Forall_forall.
Admitted.

Lemma Forall2_consE {X Y: Type} {R: X -> Y -> Prop} {x y l1 l2} : Forall2 R (x :: l1) (y :: l2) -> R x y /\ Forall2 R l1 l2.
Proof.
move=> H.
Admitted.

Lemma Forall2_length_eq {X Y: Type} {R: X -> Y -> Prop} {l1 l2} : Forall2 R l1 l2 -> length l1 = length l2.
Proof.
elim: l1 l2.
-
move=> [| ? ?] H; first done.
by inversion H.
-
move=> ? ? IH [| ? ?] /= H; inversion H.
congr S.
Admitted.

Lemma in_app_l {X: Type} {x: X} {l1 l2: list X} : In x l1 -> In x (l1 ++ l2).
Proof.
move=> ?.
apply /in_app_iff.
Admitted.

Lemma in_app_r {X: Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof.
move=> ?.
apply /in_app_iff.
Admitted.

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
Admitted.

Lemma Forall_appP {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
elim: A; first by (constructor; by [|case]).
move=> ? ? IH /=.
by rewrite ?Forall_consP IH and_assoc.
