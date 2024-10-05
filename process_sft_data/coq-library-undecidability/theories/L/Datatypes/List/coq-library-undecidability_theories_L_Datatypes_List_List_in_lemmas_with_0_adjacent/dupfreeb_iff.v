From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L Require Import UpToC.
From Undecidability.L Require Import Functions.EqBool.
From Undecidability.L.Datatypes Require Export List.List_enc.
Set Default Proof Using "Type".
Section list_in.
Variable (X : Type).
Variable (eqb : X -> X -> bool).
Variable eqb_correct : forall a b, a = b <-> eqb a b = true.
Definition list_in_decb := fix rec (l : list X) (x : X) : bool := match l with [] => false | (l :: ls) => eqb l x || rec ls x end.
Fixpoint list_incl_decb (a b : list X) := match a with | [] => true | (x::a) => list_in_decb b x && list_incl_decb a b end.
End list_in.
Section list_in_time.
Variable (X : Type).
Context {H : registered X}.
Context (eqbX : X -> X -> bool).
Context {Xeq : eqbClass eqbX}.
Context {XeqbComp : eqbCompT X}.
Definition c__listInDecb := 21.
Fixpoint list_in_decb_time (l : list X) (e : X) := match l with | [] => c__listInDecb | x :: l => eqbTime (X := X) (size (enc x)) (size (enc e)) + c__listInDecb + list_in_decb_time l e end.
Global Instance term_list_in_decb : computableTime' (@list_in_decb X eqbX) (fun l _ => (5, fun x _ => (list_in_decb_time l x, tt))).
Proof.
extract.
solverec.
all: unfold c__listInDecb; solverec.
Definition c__list_incl_decb := 22.
Fixpoint list_incl_decb_time (a b : list X) := match a with | [] => c__list_incl_decb | (x::a) => list_in_decb_time b x + list_incl_decb_time a b + c__list_incl_decb end.
Global Instance term_list_incl_decb : computableTime' (@list_incl_decb X eqbX) (fun a _ => (5, fun b _ => (list_incl_decb_time a b, tt))).
Proof.
extract.
solverec.
all: unfold c__list_incl_decb; solverec.
End list_in_time.
Section dupfree_dec.
Variable (X : Type).
Variable (eqbX : X -> X -> bool).
Variable (eqbX_correct : forall a b, a = b <-> eqbX a b = true).
Fixpoint dupfreeb (l : list X) : bool := match l with [] => true | (x :: ls) => negb (list_in_decb eqbX ls x) && dupfreeb ls end.
End dupfree_dec.
Section dupfree_dec_time.
Context {X : Type}.
Context {H : registered X}.
Context (eqbX : X -> X -> bool).
Context {Xeq : eqbClass eqbX}.
Context {XeqbComp : eqbCompT X}.
Definition c__dupfreeb := 25.
Fixpoint dupfreeb_time (l : list X) := match l with | [] => c__dupfreeb | l :: ls => list_in_decb_time ls l + c__dupfreeb + dupfreeb_time ls end.
Global Instance term_dupfreeb: computableTime' (@dupfreeb X eqbX) (fun l _ => (dupfreeb_time l, tt)).
Proof.
extract.
solverec.
all: unfold c__dupfreeb; solverec.
End dupfree_dec_time.

Lemma dupfreeb_iff (l : list X) : dupfreeb l = true <-> dupfree l.
Proof using eqbX_correct.
specialize (dupfreeb_correct l) as H0.
destruct dupfreeb.
inv H0.
split; eauto.
inv H0; split; eauto.
