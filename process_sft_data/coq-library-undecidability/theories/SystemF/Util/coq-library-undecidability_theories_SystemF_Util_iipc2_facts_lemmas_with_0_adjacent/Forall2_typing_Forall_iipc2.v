Require Import List Lia.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts typing_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.
Definition iipc2 (Gamma: environment) (t: poly_type) := exists P, typing Gamma P t.
Arguments iipc2 : simpl never.

Lemma Forall2_typing_Forall_iipc2 {Gamma Ps ts} : Forall2 (typing Gamma) Ps ts -> Forall (iipc2 Gamma) ts.
Proof.
elim; [by constructor | by move=> > /iipc2I; constructor].
