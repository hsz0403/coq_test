Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations.
Set Implicit Arguments.
Record fo_signature := Mk_fo_signature { syms : Type; rels : Type; ar_syms : syms -> nat; ar_rels : rels -> nat }.
Definition Σrel (n : nat) : fo_signature.
Proof.
exists Empty_set (* No function or constant symbols *) unit (* And one n-ary relational symbol *) .
+
intros [].
+
exact (fun _ => n).
Defined.
Definition Σrel_eq (n : nat) : fo_signature.
Proof.
exists Empty_set (* No function or constant symbols *) bool (* One ternary and equality *) .
+
intros [].
+
exact (fun b => if b then n else 2).
Defined.
Inductive Σbpcp_syms := | Σbpcp_bool : bool -> Σbpcp_syms (* shortcut is fb _ *) | Σbpcp_unit : Σbpcp_syms (* shortcut is fe *) | Σbpcp_undef : Σbpcp_syms (* shortcut is *) .
Inductive Σbpcp_rels := | Σbpcp_hand : Σbpcp_rels (* shortcut is p_P *) | Σbpcp_ssfx : Σbpcp_rels (* shortcut is p_lt *) | Σbpcp_eq : Σbpcp_rels (* shortcut is p_eq *) .
Definition Σbpcp : fo_signature.
Proof.
exists Σbpcp_syms Σbpcp_rels.
+
exact (fun s => match s with | Σbpcp_bool _ => 1 | _ => 0 end).
+
exact (fun _ => 2).
Defined.
Record fo_model Σ (X : Type) := Mk_fo_model { fom_syms : forall s, vec X (ar_syms Σ s) -> X; fom_rels : forall r, vec X (ar_rels Σ r) -> Prop }.
Definition fo_model_dec Σ X (M : fo_model Σ X) := forall r (v : vec _ (ar_rels _ r)), { fom_rels M r v } + { ~ fom_rels M r v }.
Definition rel2_on_vec X (R : X -> X -> Prop) (v : vec X 2) : Prop := R (vec_head v) (vec_head (vec_tail v)).
Arguments rel2_on_vec {X} R v /.
Section bin_rel_Σ2.
Variable (X : Type) (R : X -> X -> Prop).
Definition bin_rel_Σ2 : fo_model (Σrel 2) X.
Proof.
exists; intros [].
exact (rel2_on_vec R).
Defined.
Hypothesis HR : forall x y, { R x y } + { ~ R x y }.
Fact bin_rel_Σ2_dec : fo_model_dec bin_rel_Σ2.
Proof.
intros [] v; apply HR.
End bin_rel_Σ2.

Definition Σrel (n : nat) : fo_signature.
Proof.
exists Empty_set (* No function or constant symbols *) unit (* And one n-ary relational symbol *) .
+
intros [].
+
Admitted.

Definition Σbpcp : fo_signature.
Proof.
exists Σbpcp_syms Σbpcp_rels.
+
exact (fun s => match s with | Σbpcp_bool _ => 1 | _ => 0 end).
+
Admitted.

Definition bin_rel_Σ2 : fo_model (Σrel 2) X.
Proof.
exists; intros [].
Admitted.

Fact bin_rel_Σ2_dec : fo_model_dec bin_rel_Σ2.
Proof.
Admitted.

Definition Σrel_eq (n : nat) : fo_signature.
Proof.
exists Empty_set (* No function or constant symbols *) bool (* One ternary and equality *) .
+
intros [].
+
exact (fun b => if b then n else 2).
