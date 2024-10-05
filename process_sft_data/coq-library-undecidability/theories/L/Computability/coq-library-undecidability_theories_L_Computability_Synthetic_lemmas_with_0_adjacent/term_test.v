From Undecidability.L Require Import Computability.MuRec.
From Undecidability.L.Datatypes Require Import LNat LOptions LProd Lists.
From Undecidability.Synthetic Require Import DecidabilityFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
Require Import Datatypes.
Inductive is_computable {A} {t : TT A} (a : A) : Prop := C : computable a -> is_computable a.
Notation enumerates f p := (forall x, p x <-> exists n : nat, f n = Some x).
Definition L_decidable {X} `{registered X} (P : X -> Prop) := exists f : X -> bool, is_computable f /\ forall x, P x <-> f x = true.
Definition L_enumerable {X} `{registered X} (p : X -> Prop) := exists f : nat -> option X, is_computable f /\ (enumerates f p).
Definition L_recognisable {X} `{registered X} (p : X -> Prop) := exists f : X -> nat -> bool, is_computable f /\ forall x, p x <-> exists n, f x n = true.
Definition L_recognisable' {X} `{registered X} (p : X -> Prop) := exists s : term, forall x, p x <-> converges (L.app s (enc x)).
Section L_enum_rec.
Variable X : Type.
Context `{registered X}.
Variable (p : X -> Prop).
Hypotheses (f : nat -> option X) (c_f : computable f) (H_f : enumerates f p).
Hypotheses (d : X -> X -> bool) (c_d : computable d) (H_d : forall x y, reflect (x = y) (d x y)).
Definition test := (fun x n => match f n with Some y => d x y | None => false end).
Instance term_test : computable test.
Proof using c_f c_d.
extract.
Import HOAS_Notations.
End L_enum_rec.
Definition opt_to_list n := match nat_enum n with Some x => [x] | None => [] end.
Instance term_opt_to_list : computable opt_to_list.
Proof.
extract.
Definition L_nat := cumul (opt_to_list).
Instance term_L_nat : computable L_nat.
Proof.
unfold L_nat.
unfold cumul.
extract.
Require Import Undecidability.Shared.embed_nat Nat.
Definition F' := (fix F (n : nat) : nat := match n with | 0 => 0 | S n0 => S n0 + F n0 end).
Instance term_F' : computable F'.
Proof.
extract.
Definition F'' := (fix F (n0 : nat) : nat * nat := match n0 with | 0 => (0, 0) | S n1 => match F n1 with | (0, y) => (S y, 0) | (S x0, y) => (x0, S y) end end).
Instance term_F'' : computable F''.
Proof.
extract.
Instance term_embed_nat : computable embed.
Proof.
change (computable (fun '(x, y) => y + F' (y + x))).
extract.
Instance term_unembed_nat : computable unembed.
Proof.
unfold unembed.
change (computable F'').
exact term_F''.
Definition lenumerates {X} L (p : X -> Prop) := cumulative L /\ (forall x : X, p x <-> (exists m : nat, x el L m)).
Definition L_enum {X} `{registered X} (p : X -> Prop) := exists L, is_computable L /\ lenumerates L p.
Definition F1 {X} (T : nat -> list X) := (fun n => let (n, m) := unembed n in nth_error (T n) m).
Instance term_F1 {X} {H : registered X} : @computable ((nat -> list X) -> nat -> option X) ((! nat ~> ! list X) ~> ! nat ~> ! option X) (@F1 X).
Proof.
extract.
Import L_Notations.

Instance term_test : computable test.
Proof using c_f c_d.
extract.
