Require Import List Arith Bool Eqdep_dec.
Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.ReducibilityFacts.
Require Import Undecidability.Synthetic.InformativeDefinitions Undecidability.Synthetic.InformativeReducibilityFacts.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils fol_ops.
Set Implicit Arguments.
Definition decidable (P : Prop) := { P } + { ~ P }.
Fact decidable_bool_eq P : (decidable P -> { Q : bool | P <-> Q = true }) * ({ Q : bool | P <-> Q = true } -> decidable P).
Proof.
split.
+
intros H; exists (if H then true else false); destruct H; split; auto; discriminate.
+
intros (Q & HQ); destruct Q; [ left | right ]; rewrite HQ; auto.
Fact ireduction_decidable X Y (p : X -> Prop) (q : Y -> Prop) : p ⪯ᵢ q -> (forall y, decidable (q y)) -> forall x, decidable (p x).
Proof.
unfold decidable, decider, inf_reduces, reduction.
intros (f & Hf) Hq x.
destruct (Hq (f x)); [ left | right ]; rewrite Hf; auto.
Definition discrete X := forall x y : X, decidable (x=y).
Fact discrete_unit : discrete unit.
Proof.
intros [] []; left; auto.
Local Ltac mydecideeq := unfold discrete, decidable; intro; decide equality.
Fact discrete_opt X : discrete X -> discrete (option X).
Proof.
mydecideeq.
Fact discrete_sum X Y : discrete X -> discrete Y -> discrete (X+Y).
Proof.
mydecideeq.
Fact discrete_prod X Y : discrete X -> discrete Y -> discrete (X*Y).
Proof.
mydecideeq.
Fact discrete_list X : discrete X -> discrete (list X).
Proof.
mydecideeq.
Fact discrete_pos n : discrete (pos n).
Proof.
unfold discrete, decidable; apply pos_eq_dec.
Fact discrete_vec X n : discrete X -> discrete (vec X n).
Proof.
unfold discrete, decidable; intros; apply vec_eq_dec; auto.
Hint Resolve discrete_unit discrete_sum discrete_prod discrete_list discrete_pos discrete_vec : core.
Section decidable_fun_pos_bool.
Variable (n : nat) (K : (pos n -> bool) -> Prop) (HK : forall P Q, (forall x, P x = Q x) -> K P <-> K Q) (D : forall P, decidable (K P)).
Let Dfa : decidable (forall v, K (vec_pos v)).
Proof.
apply (fol_quant_sem_dec fol_fa).
+
apply finite_t_vec, finite_t_bool.
+
intros v; apply D.
Let Dex : decidable (exists v, K (vec_pos v)).
Proof.
apply (fol_quant_sem_dec fol_ex).
+
apply finite_t_vec, finite_t_bool.
+
intros v; apply D.
End decidable_fun_pos_bool.
Section decidable_fun_finite_bool.
Variable (X : Type) (H1 : finite_t X) (H2 : discrete X) (K : (X -> bool) -> Prop) (HK : forall P Q, (forall x, P x = Q x) -> K P <-> K Q) (Dec : forall P, decidable (K P)).
Let D : { n : nat & bij_t X (pos n) }.
Proof.
apply finite_t_discrete_bij_t_pos; auto.
Let n := projT1 D.
Let i : X -> pos n := projT1 (projT2 D).
Let j : pos n -> X := proj1_sig (projT2 (projT2 D)).
Let Hji : forall x, j (i x) = x.
Proof.
apply (proj2_sig (projT2 (projT2 D))).
Let Hij : forall y, i (j y) = y.
Proof.
apply (proj2_sig (projT2 (projT2 D))).
Let T P := K (fun p => P (i p)).
Let T_ext P Q : (forall x, P x = Q x) -> T P <-> T Q.
Proof.
intros H; apply HK; intro; apply H.
Let T_dec P : decidable (T P).
Proof.
apply Dec.
End decidable_fun_finite_bool.
Section decidable_upto.
Variable (X : Type) (R : X -> X -> Prop) (P : X -> Prop) (HP : forall x, decidable (P x)) (HR : forall x y, R x y -> P x <-> P y).
End decidable_upto.
Definition fun_ext X Y (f g : X -> Y) := forall x, f x = g x.
Definition prop_ext X (f g : X -> Prop) := forall x, f x <-> g x.
Section fun_pos_finite_t_upto.
Variable (X : Type) (HX : finite_t X).
End fun_pos_finite_t_upto.
Section fun_finite_t_upto.
Variable (X : Type) (HX1 : finite_t X) (HX2 : discrete X) (Y : Type) (HY : finite_t Y).
Let D : { n : nat & bij_t X (pos n) }.
Proof.
apply finite_t_discrete_bij_t_pos; auto.
End fun_finite_t_upto.
Section dec_pred_finite_t_upto.
Variable (X : Type) (HX1 : finite_t X) (HX2 : discrete X).
Hint Resolve finite_t_bool : core.
Let bool_prop (f : X -> bool) : { p : X -> Prop & forall x, decidable (p x) }.
Proof.
exists (fun x => f x = true).
intro; apply bool_dec.
Defined.
End dec_pred_finite_t_upto.
Section finite_t_valuations.
Variable (X : Type) (HX1 : finite_t X) (HX2 : discrete X) (x : X).
Implicit Type (ln : list nat).
Let R ln (f g : nat -> X) := forall n, In n ln -> f n = g n.
Let combine (n : nat) : (X * (nat -> X)) -> nat -> X.
Proof.
intros (x', f) m.
destruct (eq_nat_dec n m).
+
exact x'.
+
apply (f m).
Defined.
End finite_t_valuations.
Section finite_t_model.
Variable (syms : Type) (ar : syms -> nat) (Hsyms : discrete syms) (X : Type) (HX1 : finite_t X) (HX2 : discrete X) (Y : Type) (HY : finite_t Y) (y : Y).
Implicit Type (ls : list syms).
Let funs := forall s, vec X (ar s) -> Y.
Let R ls (s1 s2 : funs) := forall s, In s ls -> forall v, @s1 s v = s2 s v.
Hint Resolve finite_t_vec vec_eq_dec : core.
Let fun_combine s (f : vec X (ar s) -> Y) (g : funs) : funs.
Proof.
intros s'.
destruct (Hsyms s s').
+
subst s; exact f.
+
apply g.
Defined.
End finite_t_model.

Fact decidable_bool_eq P : (decidable P -> { Q : bool | P <-> Q = true }) * ({ Q : bool | P <-> Q = true } -> decidable P).
Proof.
split.
+
intros H; exists (if H then true else false); destruct H; split; auto; discriminate.
+
Admitted.

Fact ireduction_decidable X Y (p : X -> Prop) (q : Y -> Prop) : p ⪯ᵢ q -> (forall y, decidable (q y)) -> forall x, decidable (p x).
Proof.
unfold decidable, decider, inf_reduces, reduction.
intros (f & Hf) Hq x.
Admitted.

Fact discrete_unit : discrete unit.
Proof.
Admitted.

Fact discrete_opt X : discrete X -> discrete (option X).
Proof.
Admitted.

Fact discrete_sum X Y : discrete X -> discrete Y -> discrete (X+Y).
Proof.
Admitted.

Fact discrete_prod X Y : discrete X -> discrete Y -> discrete (X*Y).
Proof.
Admitted.

Fact discrete_list X : discrete X -> discrete (list X).
Proof.
Admitted.

Fact discrete_pos n : discrete (pos n).
Proof.
Admitted.

Let Dfa : decidable (forall v, K (vec_pos v)).
Proof.
apply (fol_quant_sem_dec fol_fa).
+
apply finite_t_vec, finite_t_bool.
+
Admitted.

Let Dex : decidable (exists v, K (vec_pos v)).
Proof.
apply (fol_quant_sem_dec fol_ex).
+
apply finite_t_vec, finite_t_bool.
+
Admitted.

Theorem fa_fun_pos_bool_decidable : decidable (forall P, K P).
Proof.
destruct Dfa as [ H | H ].
+
left.
intros P; generalize (H (vec_set_pos P)).
apply HK; intro; rew vec.
+
right; contradict H.
Admitted.

Theorem ex_fun_pos_bool_decidable : decidable (exists P, K P).
Proof.
destruct Dex as [ H | H ].
+
left.
destruct H as (v & Hv).
exists (vec_pos v); auto.
+
right; contradict H.
destruct H as (P & HP).
exists (vec_set_pos P).
revert HP; apply HK.
Admitted.

Let D : { n : nat & bij_t X (pos n) }.
Proof.
Admitted.

Let Hji : forall x, j (i x) = x.
Proof.
Admitted.

Let Hij : forall y, i (j y) = y.
Proof.
Admitted.

Let T_ext P Q : (forall x, P x = Q x) -> T P <-> T Q.
Proof.
Admitted.

Let T_dec P : decidable (T P).
Proof.
Admitted.

Theorem fa_fun_bool_decidable : decidable (forall P, K P).
Proof.
assert (H : decidable (forall P, T P)).
{
apply fa_fun_pos_bool_decidable; auto.
}
destruct H as [ H | H ]; [ left | right ].
+
intros P.
generalize (H (fun p => P (j p))).
apply HK; intro; rewrite Hji; auto.
+
Admitted.

Fact discrete_vec X n : discrete X -> discrete (vec X n).
Proof.
unfold discrete, decidable; intros; apply vec_eq_dec; auto.
