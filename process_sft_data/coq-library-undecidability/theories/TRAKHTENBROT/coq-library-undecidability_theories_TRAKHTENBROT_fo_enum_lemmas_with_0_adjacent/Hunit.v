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

Let Hunit : opt_enum_t (fun _ : unit => True).
Proof.
apply type_enum_opt_enum_t.
exists (fun _ => Some tt).
intros []; exists 0; auto.
