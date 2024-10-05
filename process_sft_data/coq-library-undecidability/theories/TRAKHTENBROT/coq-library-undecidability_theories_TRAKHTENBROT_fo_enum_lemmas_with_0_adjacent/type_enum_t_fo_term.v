Require Import List Arith Lia Max.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils decidable enumerable fol_ops fo_sig fo_terms fo_logic.
Set Implicit Arguments.
Section fol_enumerable.
Variable (Σ : fo_signature) (H1 : discrete (syms Σ)) (H2 : discrete (rels Σ)) (H3 : type_enum_t (syms Σ)) (H4 : type_enum_t (rels Σ)).
Let Hunit : opt_enum_t (fun _ : unit => True).
Proof.
apply type_enum_opt_enum_t.
exists (fun _ => Some tt).
intros []; exists 0; auto.
Let Hnat : opt_enum_t (fun _ : nat => True).
Proof.
apply type_enum_opt_enum_t.
exists Some.
intros n; exists n; auto.
Let Hfol_bop : opt_enum_t (fun _ : fol_bop => True).
Proof.
apply type_enum_opt_enum_t.
exists (fun n => Some (match n with 0 => fol_conj | 1 => fol_disj | _ => fol_imp end)).
intros [].
+
exists 0; auto.
+
exists 1; auto.
+
exists 2; auto.
Let Hfol_qop : opt_enum_t (fun _ : fol_qop => True).
Proof.
apply type_enum_opt_enum_t.
exists (fun n => Some (match n with 0 => fol_fa | _ => fol_ex end)).
intros [].
+
exists 1; auto.
+
exists 0; auto.
End fol_enumerable.

Lemma type_enum_t_fo_term : type_enum_t (fo_term (ar_syms Σ)).
Proof.
apply type_enum_t_by_measure with (m := @fo_term_height _ _).
induction n as [ | n Hn ].
+
generalize Hnat.
apply opt_enum_t_image with in_var.
intros [ i | s v ]; simpl.
*
split; auto; exists i; auto.
*
split; try lia; intros (? & _ & ?); discriminate.
+
generalize (opt_enum_t_dep_sum _ _ H1 H3 (fun s => opt_enum_t_vec (ar_syms Σ s) Hn)); intros H5.
generalize (opt_enum_t_sum Hnat H5).
apply opt_enum_t_image with (f := fun p => match p with | inl i => in_var i | inr (existT _ s v) => @in_fot _ _ s v end).
intros t; split.
*
destruct t as [ i | s v ]; intros H.
-
exists (inl i); auto.
-
exists (inr (existT _ s v)); simpl; split; auto.
intros p; generalize (fo_term_height_lt _ v p); lia.
*
intros ([ i | (s,v) ] & H); revert H; simpl.
-
intros (_ & ->); simpl; lia.
-
intros (G & ->); simpl; apply le_n_S, lmax_spec, Forall_forall.
intros x Hx; apply vec_list_inv in Hx.
destruct Hx as (p & Hp); revert Hp; rew vec; intros ->; auto.
