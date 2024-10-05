Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments measure_ind {X}.
Arguments measure_rect {X}.

Lemma copy {A : Prop} : A -> A * A.
Proof.
done.
