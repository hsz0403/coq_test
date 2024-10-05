Require Import Lia.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Arguments measure_ind {X}.
Arguments measure_rect {X}.

Lemma unnest (X Y Z: Type): X -> (Y -> Z) -> (X -> Y) -> Z.
Proof.
by auto.
