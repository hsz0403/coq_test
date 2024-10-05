Require Import List Arith Bool Lia Eqdep_dec.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat decidable fo_sat_dec.
Set Implicit Arguments.
Local Notation ø := vec_nil.
Section Σ1_model.
Variable (V : Type) (n : nat) (HV : V -> False).
Definition ΣP1 : fo_signature.
Proof.
exists V (pos n); intros _.
+
exact 1.
+
exact 1.
Defined.
Variable (X : Type) (M : fo_model ΣP1 X) (HX : finite_t X) (Mdec : fo_model_dec M).
Let f p (x : X) := if Mdec (r := p) (x##ø) then true else false.
Let Q (v : vec bool n) := exists x, forall p, f p x = vec_pos v p.
Let Q_dec v : { Q v } + { ~ Q v }.
Proof.
unfold Q.
apply (fol_quant_sem_dec fol_ex); auto; intros x.
apply (fol_quant_sem_dec fol_fa); auto.
+
apply finite_t_pos.
+
intro; apply bool_dec.
Let K v := if Q_dec v then true else false.
Let HK v : K v = true <-> Q v.
Proof.
unfold K.
destruct (Q_dec v); split; try tauto; discriminate.
Let Kf x : K (vec_set_pos (fun p => f p x)) = true.
Proof.
apply HK; exists x; intros; rew vec.
Let M' : fo_model ΣP1 (sig (fun v => K v = true)).
Proof.
split.
+
intros s; destruct (HV s).
+
simpl; intros p v.
exact (vec_pos (proj1_sig (vec_head v)) p = true).
Defined.
Let R : @fo_simulation ΣP1 (nil) (pos_list n) _ M _ M'.
Proof.
exists (fun x v => forall p, f p x = vec_pos (proj1_sig v) p).
+
intros s; destruct (HV s).
+
intros p; simpl; intros v w _ H.
generalize (H pos0); simpl; clear H.
vec split v with x; vec nil v; clear v.
vec split w with y; vec nil w; clear w.
destruct y as [ v Hv ]; simpl; intros Hx.
generalize (Hx p); unfold f; clear Hx.
destruct (Mdec (x##ø)); split; try easy.
intros E; rewrite E in *; discriminate.
+
intros x.
exists (exist _ (vec_set_pos (fun p => f p x)) (Kf x)); intros p; simpl; rew vec.
+
intros (v & Hv).
unfold K in Hv; simpl; auto.
destruct (Q_dec v); auto; discriminate.
Defined.
Variable rho : nat -> X.
Let psi n : sig (fun v => K v = true) := exist _ _ (Kf (rho n)).
Let equiv (A : fol_form ΣP1) : fol_sem M rho A <-> fol_sem M' psi A.
Proof.
apply fo_model_simulation with (R := R).
+
intros s; destruct (HV s).
+
intros p _; apply pos_list_prop.
+
intros i _ p; unfold psi, R; simpl; rew vec.
Variable (A : fol_form ΣP1) (HA : fol_sem M rho A).
Local Theorem bounded_model : exists (Q : vec bool n -> bool) (M' : fo_model ΣP1 (sig (fun v => Q v = true))) (_ : fo_model_dec M') psi, fol_sem M' psi A.
Proof.
exists K, M'.
exists.
{
unfold M'; intros p v; simpl; apply bool_dec.
}
exists psi; apply equiv, HA.
End Σ1_model.

Definition ΣP1 : fo_signature.
Proof.
exists V (pos n); intros _.
+
exact 1.
+
exact 1.
