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

Lemma semi_decidable_enumerable {X} {p : X -> Prop} : enumerable__T X -> semi_decidable p -> enumerable p.
Proof.
unfold semi_decidable, semi_decider.
intros [e He] [f Hf].
exists (fun p => let (n, m) := unembed p in if! e n is Some x then if f x m then Some x else None else None).
intros x.
rewrite Hf.
split.
-
intros [n Hn].
destruct (He x) as [m Hm].
exists (embed (m,n)).
now rewrite embedP, Hm, Hn.
-
intros [mn Hmn].
destruct (unembed mn) as (m, n).
destruct (e m) as [x'|]; try congruence.
destruct (f x' n) eqn:E; inversion Hmn.
subst.
exists n.
exact E.
