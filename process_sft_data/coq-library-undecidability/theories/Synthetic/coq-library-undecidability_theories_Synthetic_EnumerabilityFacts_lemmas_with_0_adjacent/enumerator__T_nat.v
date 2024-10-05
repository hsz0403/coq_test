From Undecidability.Synthetic Require Import DecidabilityFacts SemiDecidabilityFacts.
From Undecidability.Shared Require Import embed_nat.
Local Notation "'if!' x 'is' p 'then' a 'else' b" := (match x with p => a | _ => b end) (at level 0, p pattern).
Definition enumerator__T' X f := forall x : X, exists n : nat, f n = Some x.
Notation enumerator__T f X := (enumerator__T' X f).
Definition enumerable__T X := exists f : nat -> option X, enumerator__T f X.
Definition nat_enum (n : nat) := Some n.
Definition unit_enum (n : nat) := Some tt.
Definition bool_enum (n : nat) := Some (if! n is 0 then true else false).
Definition prod_enum {X Y} (f1 : nat -> option X) (f2 : nat -> option Y) n : option (X * Y) := let (n, m) := unembed n in if! (f1 n, f2 m) is (Some x, Some y) then Some (x, y) else None.
Definition option_enum {X} (f : nat -> option X) n := match n with 0 => Some None | S n => Some (f n) end.
Existing Class enumerator__T'.
Hint Resolve enumerator_enumerable : core.
Existing Instance enumerator__T_prod.
Existing Instance enumerator__T_option.
Existing Instance enumerator__T_bool.
Existing Instance enumerator__T_nat.

Lemma enumerator__T_nat : enumerator__T nat_enum nat.
Proof.
intros n.
cbv.
eauto.
