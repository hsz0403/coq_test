Require Import List.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".

Lemma Forall_mapP {X Y : Type} {P : Y -> Prop} {f : X -> Y} {l : list X} : Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
elim: l; [ constructor; by constructor | ].
move=> ? ? IH /=.
constructor => /ForallE [? /IH ?]; by constructor.
