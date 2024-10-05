Require Import List.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Definition Forall_norm := (@Forall_app_iff, @Forall_singleton_iff, @Forall_cons_iff, @Forall_nil_iff).

Lemma copy {A: Prop} : A -> A * A.
Proof.
Admitted.

Lemma itebP {X: Type} {P: bool -> X} {b: bool} : (if b then P true else P false) = P b.
Proof.
Admitted.

Lemma Forall_nil_iff {X: Type} {P: X -> Prop} : Forall P [] <-> True.
Proof.
Admitted.

Lemma Forall_cons_iff {T: Type} {P: T -> Prop} {a l} : Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
constructor.
-
move=> H.
by inversion H.
-
move=> [? ?].
Admitted.

Lemma Forall_singleton_iff {X: Type} {P: X -> Prop} {x} : Forall P [x] <-> P x.
Proof.
rewrite Forall_cons_iff.
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

Lemma Forall_app_iff {T: Type} {P: T -> Prop} {A B}: Forall P (A ++ B) <-> Forall P A /\ Forall P B.
Proof.
elim: A.
-
constructor; by [|case].
-
move=> ? ? IH /=.
rewrite ? Forall_cons_iff ? IH.
by tauto.
