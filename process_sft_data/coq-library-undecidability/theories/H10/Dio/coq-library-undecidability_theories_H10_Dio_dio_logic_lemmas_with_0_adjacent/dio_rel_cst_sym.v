Require Import Arith Nat ZArith Lia.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac gcd sums bounded_quantification.
Set Implicit Arguments.
Set Default Proof Using "Type".
Definition de_bruijn_ext {X} (ν : nat -> X) x := fix dbe n := match n with | 0 => x | S n => ν n end.
Notation "x · ν" := (de_bruijn_ext ν x) (at level 1, format "x · ν", left associativity).
Notation "ν ⭳" := (fun n => ν (S n)) (at level 1, format "ν ⭳", no associativity).
Fact de_bruijn_ext_proj X (ν : nat -> X) x n : (x·ν)⭳ n = ν n.
Proof.
reflexivity.
Fact de_bruijn_proj_ext X (ν : nat -> X) n : (ν 0)·(ν⭳) n = ν n.
Proof.
destruct n; reflexivity.
Inductive dio_op := do_add | do_mul.
Definition de_op_sem (o : dio_op) := match o with | do_add => plus | do_mul => mult end.
Definition df_op_sem (o : dio_op) := match o with | do_add => or | do_mul => and end.
Inductive dio_formula : Set := | df_cst : forall (x : nat) (n : nat), dio_formula | df_eq : forall (x y : nat), dio_formula | df_op : forall (o : dio_op) (x y z : nat), dio_formula | df_bin : forall (o : dio_op) (f g : dio_formula), dio_formula | df_exst : dio_formula -> dio_formula.
Notation df_add := (df_op do_add).
Notation df_mul := (df_op do_mul).
Notation df_conj := (df_bin do_mul).
Notation df_disj := (df_bin do_add).
Notation "∃ x" := (df_exst x) (at level 54, right associativity).
Notation "x ∧ y" := (df_conj x y) (at level 51, right associativity, format "x ∧ y").
Notation "x ∨ y" := (df_disj x y) (at level 52, right associativity, format "x ∨ y").
Local Notation "x ≐ ⌞ n ⌟" := (df_cst x n) (at level 49, no associativity, format "x ≐ ⌞ n ⌟").
Local Notation "x ≐ y" := (df_eq x y) (at level 49, no associativity, format "x ≐ y").
Local Notation "x ≐ y ⨢ z" := (df_add x y z) (at level 49, no associativity, y at next level, format "x ≐ y ⨢ z").
Local Notation "x ≐ y ⨰ z" := (df_mul x y z) (at level 49, no associativity, y at next level, format "x ≐ y ⨰ z").
Local Reserved Notation "'⟦' t '⟧'" (at level 1, format "⟦ t ⟧").
Local Reserved Notation "f '⦃' σ '⦄'" (at level 1, format "f ⦃ σ ⦄").
Section diophantine_logic_basics.
Fixpoint df_size f := match f with | df_cst _ _ => 3 | df_eq _ _ => 3 | df_op _ _ _ _ => 5 | df_bin _ f g => 1 + df_size f + df_size g | df_exst f => 1 + df_size f end.
Fixpoint df_size_Z f := (match f with | df_cst _ _ => 3 | df_eq _ _ => 3 | df_op _ _ _ _ => 5 | df_bin _ f g => 1 + df_size_Z f + df_size_Z g | df_exst f => 1 + df_size_Z f end)%Z.
Fact df_size_Z_spec f : df_size_Z f = Z.of_nat (df_size f).
Proof.
induction f as [ | | | ? f Hf g Hg | f Hf ]; simpl df_size; rewrite Nat2Z.inj_succ; try rewrite Nat2Z.inj_add; unfold df_size_Z; fold df_size_Z; auto; try lia.
Fixpoint df_pred f ν := match f with | df_cst x n => ν x = n | df_eq x y => ν x = ν y | df_op o x y z => ν x = de_op_sem o (ν y) (ν z) | df_bin o f g => df_op_sem o (⟦f⟧ ν) (⟦g⟧ ν) | df_exst f => exists n, ⟦f⟧ n·ν end where "⟦ f ⟧" := (df_pred f).
Fact df_pred_cst x n ν : ⟦x ≐ ⌞n⌟⟧ ν = (ν x = n).
Proof.
reflexivity.
Fact df_pred_eq x y ν : ⟦x ≐ y⟧ ν = (ν x = ν y).
Proof.
reflexivity.
Fact df_pred_add x y z ν : ⟦x ≐ y ⨢ z⟧ ν = (ν x = ν y + ν z).
Proof.
reflexivity.
Fact df_pred_mul x y z ν : ⟦x ≐ y ⨰ z⟧ ν = (ν x = ν y * ν z).
Proof.
reflexivity.
Fact df_pred_conj f g ν : ⟦f ∧ g⟧ ν = (⟦f⟧ ν /\ ⟦g⟧ ν).
Proof.
reflexivity.
Fact df_pred_disj f g ν : ⟦f ∨ g⟧ ν = (⟦f⟧ ν \/ ⟦g⟧ ν).
Proof.
reflexivity.
Fact df_pred_exst f ν : ⟦∃f⟧ ν = exists n, ⟦f⟧ n·ν.
Proof.
reflexivity.
Fact df_pred_ext f ν ω : (forall x, ν x = ω x) -> ⟦f⟧ ν <-> ⟦f⟧ ω.
Proof.
induction f as [ | | [] | [] f Hf g Hg | f Hf ] in ν, ω |- *; intros H; simpl.
1-4: rewrite !H; tauto.
1-2: rewrite Hf, Hg; auto; tauto.
split; intros (n & Hn); exists n; revert Hn; apply Hf; intros []; simpl; auto.
Definition der_lift ρ x := match x with 0 => 0 | S x => S (ρ x) end.
Fixpoint df_ren ρ f := match f with | df_cst x n => df_cst (ρ x) n | df_eq x y => df_eq (ρ x) (ρ y) | df_op o x y z => df_op o (ρ x) (ρ y) (ρ z) | df_bin o f g => df_bin o f⦃ρ⦄ g⦃ρ⦄ | df_exst f => df_exst f⦃der_lift ρ⦄ end where "f ⦃ ρ ⦄" := (df_ren ρ f).
Fact df_ren_size ρ f : df_size f⦃ρ⦄ = df_size f.
Proof.
revert ρ; induction f; intros; simpl; auto; do 2 f_equal; auto.
Fact df_ren_size_Z ρ f : df_size_Z f⦃ρ⦄ = df_size_Z f.
Proof.
do 2 rewrite df_size_Z_spec; f_equal; apply df_ren_size.
Fact df_pred_ren f ν ρ : ⟦f⦃ρ⦄⟧ ν <-> ⟦f⟧ (fun x => ν (ρ x)).
Proof.
revert ν ρ; induction f as [ | | [] | [] f Hf g Hg | f Hf ]; intros ν ρ; simpl; try tauto.
1-2: rewrite Hf, Hg; tauto.
split; intros (n & Hn); exists n; revert Hn; rewrite Hf; apply df_pred_ext; intros []; simpl; auto.
Fact df_pred_lift f ν : ⟦f⦃S⦄⟧ ν <-> ⟦f⟧ ν⭳.
Proof.
apply df_pred_ren.
End diophantine_logic_basics.
Local Notation "⟦ f ⟧" := (df_pred f).
Local Notation "f ⦃ ρ ⦄" := (df_ren ρ f).
Definition dio_rel R := { f | forall ν, ⟦f⟧ ν <-> R ν }.
Notation 𝔻R := dio_rel.
Section dio_rel_closure_properties.
Implicit Types R S : (nat -> nat) -> Prop.
Fact dio_rel_cst x n : 𝔻R (fun ν => ν x = n).
Proof.
exists (x ≐ ⌞n⌟); abstract (intro; simpl; tauto).
Defined.
Fact dio_rel_eq x y : 𝔻R (fun ν => ν x = ν y).
Proof.
exists (x ≐ y); simpl; tauto.
Defined.
Fact dio_rel_add x y z : 𝔻R (fun ν => ν x = ν y + ν z).
Proof.
exists (x ≐ y ⨢ z); abstract (intro; simpl; tauto).
Defined.
Fact dio_rel_mul x y z : 𝔻R (fun ν => ν x = ν y * ν z).
Proof.
exists (x ≐ y ⨰ z); abstract (intro; simpl; tauto).
Defined.
Fact dio_rel_conj R S : 𝔻R R -> 𝔻R S -> 𝔻R (fun ν => R ν /\ S ν).
Proof.
intros (fR & H1) (fS & H2); exists (fR ∧ fS).
abstract (intro; rewrite df_pred_conj, H1, H2; tauto).
Defined.
Fact dio_rel_disj R S : 𝔻R R -> 𝔻R S -> 𝔻R (fun ν => R ν \/ S ν).
Proof.
intros (fR & H1) (fS & H2); exists (fR ∨ fS).
abstract (intro; rewrite df_pred_disj, H1, H2; tauto).
Defined.
Fact dio_rel_exst (K : nat -> (nat -> nat) -> Prop) : 𝔻R (fun ν => K (ν 0) ν⭳) -> 𝔻R (fun ν => exists x, K x ν).
Proof.
intros (f & Hf); exists (∃f).
abstract (intros ν; rewrite df_pred_exst; split; intros (n & Hn); exists n; revert Hn; rewrite Hf; simpl; auto).
Defined.
Fact dio_rel_equiv R S : (forall ν, S ν <-> R ν) -> 𝔻R R -> 𝔻R S.
Proof.
intros H (f & Hf); exists f.
abstract (intro; rewrite Hf, H; tauto).
Defined.
Fact dio_rel_ren R ρ : 𝔻R R -> 𝔻R (fun ν => R (fun n => ν (ρ n))).
Proof.
intros (f & Hf); exists (f⦃ρ⦄).
abstract (intros; rewrite df_pred_ren, Hf; tauto).
Defined.
End dio_rel_closure_properties.
Definition dio_fun t := 𝔻R (fun ν => ν 0 = t ν⭳).
Notation 𝔻F := dio_fun.
Fact dio_fun_var x : 𝔻F (fun ν => ν x).
Proof.
apply dio_rel_eq.
Defined.
Fact dio_fun_cst c : 𝔻F (fun _ => c).
Proof.
red; apply dio_rel_cst.
Defined.
Fact dio_fun_add_im x y : 𝔻F (fun ν => ν x + ν y).
Proof.
apply dio_rel_add.
Defined.
Fact dio_fun_mul_im x y : 𝔻F (fun ν => ν x * ν y).
Proof.
apply dio_rel_mul.
Defined.
Fact dio_fun_equiv r s : (forall ν, s ν = r ν) -> 𝔻F r -> 𝔻F s.
Proof.
intros H1; apply dio_rel_equiv.
abstract (intro; rewrite H1; tauto).
Defined.
Fact dio_fun_ren t f : 𝔻F t -> 𝔻F (fun ν => t (fun n => ν (f n))).
Proof.
apply dio_rel_ren with (ρ := der_lift f).
Defined.
Section utilities_for_better_efficiency.
Ltac dio_sym H := now (apply dio_rel_equiv with (2 := H)).
Fact dio_rel_cst_sym x n : 𝔻R (fun ν => n = ν x).
Proof.
dio_sym (dio_rel_cst x n).
Defined.
Fact dio_rel_add_sym x y z : 𝔻R (fun ν => ν y + ν z = ν x).
Proof.
dio_sym (dio_rel_add x y z).
Defined.
Fact dio_rel_mul_sym x y z : 𝔻R (fun ν => ν y * ν z = ν x).
Proof.
dio_sym (dio_rel_mul x y z).
Defined.
Fact dio_rel_fun x t : 𝔻F t -> 𝔻R (fun ν => ν x = t ν).
Proof.
apply dio_rel_ren with (ρ := fun n => match n with | 0 => x | S n => n end).
Defined.
Fact dio_rel_fun_sym x t : 𝔻F t -> 𝔻R (fun ν => t ν = ν x).
Proof.
intros H; dio_sym (dio_rel_fun x H).
Defined.
End utilities_for_better_efficiency.
Fact dio_rel_fun_eq r t : 𝔻F r -> 𝔻F t -> 𝔻R (fun ν => r ν = t ν).
Proof.
intros H1 H2; red in H1, H2.
apply dio_rel_equiv with (R := fun ν => exists x, x = r ν /\ x = t ν).
+
abstract (intros v; split; [ intros ->; exists (t v); auto | intros (? & -> & ?); auto ]).
+
apply dio_rel_exst, dio_rel_conj; auto.
Defined.
Create HintDb dio_fun_db.
Create HintDb dio_rel_db.
Create HintDb dio_rel_im_db.
Ltac dio_fun_auto := apply dio_fun_var || apply dio_fun_cst || apply dio_fun_add_im || apply dio_fun_mul_im || auto 7 with dio_fun_db (* the depth of 7 is mostly enough *) .
Ltac dio_rel_immediate := auto with dio_rel_im_db.
Ltac dio_rel_eq := apply dio_rel_fun (* x = t *) || apply dio_rel_fun_sym (* t = x *) || apply dio_rel_fun_eq (* r = t *) .
Ltac dio_rel_decompose := apply dio_rel_exst (* exists x, ... *) || apply dio_rel_conj (* ... /\ ... *) || apply dio_rel_disj (* ... \/ ... *) .
Ltac dio_rel_auto := dio_rel_immediate; auto 7 with dio_rel_db dio_fun_db; ( (dio_rel_eq; dio_fun_auto) || (dio_rel_decompose; dio_rel_auto) || idtac ).
Tactic Notation "dio" "auto" := match goal with | |- 𝔻R _ => dio_rel_auto | |- 𝔻F _ => dio_fun_auto end.
Tactic Notation "by" "dio" "equiv" uconstr(f) := match goal with | |- 𝔻R _ => apply dio_rel_equiv with (R := f); [ | dio auto ] | |- 𝔻F _ => apply dio_fun_equiv with (r := f); [ | dio auto ] end.
Tactic Notation "dio" "by" "lemma" uconstr(f) := intros; apply dio_rel_equiv with (1 := f); dio auto.
Hint Resolve dio_fun_var dio_fun_cst dio_fun_ren : dio_fun_db.
Hint Resolve dio_rel_eq dio_rel_cst dio_rel_cst_sym dio_rel_add dio_rel_add_sym dio_rel_mul dio_rel_mul_sym : dio_rel_im_db.
Fact dio_fun_plus r t : 𝔻F r -> 𝔻F t -> 𝔻F (fun ν => r ν + t ν).
Proof.
intros H1 H2; red.
by dio equiv (fun ν => exists b c, ν 0 = b + c /\ b = r ν⭳ /\ c = t ν⭳).
abstract (intros v; split; [ exists (r v⭳), (t v⭳); auto | intros (? & ? & -> & -> & ->); auto ]).
Defined.
Fact dio_fun_mult r t : 𝔻F r -> 𝔻F t -> 𝔻F (fun ν => r ν * t ν).
Proof.
intros H1 H2; red.
by dio equiv (fun ν => exists b c, ν 0 = b * c /\ b = r ν⭳ /\ c = t ν⭳).
abstract (intros v; split; [ exists (r v⭳), (t v⭳); auto | intros (? & ? & -> & -> & ->); auto ]).
Defined.
Hint Resolve dio_fun_plus dio_fun_mult : dio_fun_db.
Local Fact example_eq : 𝔻R (fun ν => ν 0 = ν 0).
Proof.
dio auto.
Defined.
Section True_False.
Hint Resolve dio_rel_cst dio_rel_add : dio_rel_db.
Fact dio_rel_True : 𝔻R (fun _ => True).
Proof.
by dio equiv (fun _ => exists x, x = 0).
abstract (split; try tauto; exists 0; auto).
Defined.
Fact dio_rel_False : 𝔻R (fun _ => False).
Proof.
by dio equiv (fun _ => exists x, x = 1 /\ x = 0).
abstract (split; try tauto; intros (? & ? & ?); lia).
Defined.
End True_False.
Hint Resolve dio_rel_True dio_rel_False : dio_rel_db.
Fact dio_rel_le_im x y : 𝔻R (fun ν => ν x <= ν y).
Proof.
by dio equiv (fun ν => exists a, ν y = a + ν x).
abstract (intros v; split; [ intros H; exists (v y - v x); lia | intros (? & ->); lia ]).
Defined.
Fact dio_rel_lt_im x y : 𝔻R (fun ν => ν x < ν y).
Proof.
by dio equiv (fun ν => exists a b c, ν y = c + ν x /\ b = 1 /\ c = a + b).
abstract (intros v; split; [ intros H; exists (v y - v x -1), 1, (v y - v x); lia | intros (? & ? & ? & -> & -> & ->); lia ]).
Defined.
Fact dio_rel_div_im x y : 𝔻R (fun ν => divides (ν x) (ν y)).
Proof.
by dio equiv (fun ν => exists a, ν y = a * ν x).
unfold divides; tauto.
Defined.
Hint Resolve dio_rel_le_im dio_rel_lt_im dio_rel_div_im : dio_rel_im_db.
Fact dio_rel_le r t : 𝔻F r -> 𝔻F t -> 𝔻R (fun ν => r ν <= t ν).
Proof.
intros H1 H2.
by dio equiv (fun ν => exists a b, a <= b /\ a = r ν /\ b = t ν).
abstract (intros v; split; [ exists (r v), (t v) | intros (? & ? & ? & -> & ->) ]; auto).
Defined.
Fact dio_rel_lt r t : 𝔻F r -> 𝔻F t -> 𝔻R (fun ν => r ν < t ν).
Proof.
intros H1 H2.
by dio equiv (fun ν => exists a b, a < b /\ a = r ν /\ b = t ν).
abstract (intros v; split; [ exists (r v), (t v) | intros (? & ? & ? & -> & ->) ]; auto).
Defined.
Hint Resolve dio_rel_lt dio_rel_le : dio_rel_db.
Fact dio_rel_neq r t : 𝔻F r -> 𝔻F t -> 𝔻R (fun ν => r ν <> t ν).
Proof.
intros H1 H2.
by dio equiv (fun v => exists a b, (a < b \/ b < a) /\ a = r v /\ b = t v).
abstract (intros v; split; [ exists (r v), (t v) | intros (? & ? & ?) ]; lia).
Defined.
Fact dio_rel_div r t : 𝔻F r -> 𝔻F t -> 𝔻R (fun ν => divides (r ν) (t ν)).
Proof.
intros H1 H2.
by dio equiv (fun v => exists a b, divides a b /\ a = r v /\ b = t v).
abstract (intros v; split; [ exists (r v), (t v) | intros (? & ? & ? & -> & ->) ]; auto).
Defined.
Hint Resolve dio_rel_neq dio_rel_div : dio_rel_db.
Local Fact example_le : 𝔻R (fun ν => ν 0 <= ν 1).
Proof.
dio auto.
Defined.
Local Fact example_lt : 𝔻R (fun ν => ν 0 < ν 1).
Proof.
dio auto.
Defined.
Local Fact example_div : 𝔻R (fun ν => divides (ν 0) (ν 1)).
Proof.
dio auto.
Defined.
Section dio_fun_rem.
Let rem_equiv p x r : r = rem x p <-> exists x' p', x' = x /\ p' = p /\ ( (p' = 0 /\ x' = r) \/ (p' <> 0 /\ r < p' /\ exists n, x' = n*p' + r) ).
Proof.
split.
+
intro; exists x, p; subst; msplit 2; auto.
destruct (eq_nat_dec p 0) as [ Hp | Hp ].
*
left; split; auto; subst; rewrite rem_0; auto.
*
right; split; auto; split.
-
apply div_rem_spec2; auto.
-
exists (div x p);apply div_rem_spec1.
+
intros (? & ? & -> & -> & [ (H1 & H2) | (H1 & H2 & n & H3) ]).
*
subst; rewrite rem_0; auto.
*
symmetry; apply rem_prop with n; auto.
Fact dio_fun_rem p x : 𝔻F p -> 𝔻F x -> 𝔻F (fun ν => rem (x ν) (p ν)).
Proof.
dio by lemma (fun v => rem_equiv (p v⭳) (x v⭳) (v 0)).
Defined.
End dio_fun_rem.
Hint Resolve dio_fun_rem : dio_fun_db.
Local Fact dio_fun_rem_example : 𝔻F (fun ν => rem (ν 0) (ν 1)).
Proof.
dio auto.
Defined.
Section dio_rel_ndivides.
Let ndivides_eq x y : ~ (divides x y) <-> x = 0 /\ y <> 0 \/ exists a b, y = a*x+b /\ 0 < b < x.
Proof.
split.
+
intros H.
destruct x as [ | x ].
*
left; split; auto; contradict H; subst; apply divides_0.
*
right; exists (div y (S x)), (rem y (S x)); split.
-
apply div_rem_spec1.
-
rewrite divides_rem_eq in H.
generalize (@div_rem_spec2 y (S x)); intros; lia.
+
intros [ (H1 & H2) | (a & b & H1 & H2) ].
*
subst; contradict H2; revert H2; apply divides_0_inv.
*
rewrite divides_rem_eq.
rewrite (div_rem_spec1 y x) in H1.
apply div_rem_uniq in H1; try lia.
apply div_rem_spec2; lia.
Fact dio_rel_ndivides x y : 𝔻F x -> 𝔻F y -> 𝔻R (fun ν => ~ divides (x ν) (y ν)).
Proof.
dio by lemma (fun v => ndivides_eq (x v) (y v)).
Defined.
End dio_rel_ndivides.
Local Fact dio_rel_ndiv_example : 𝔻R (fun ν => ~ divides (ν 0) (ν 1)).
Proof.
apply dio_rel_ndivides; dio auto.
Defined.
Section dio_rel_not_divides.
Let not_divides_eq p x : ~ divides p x <-> rem x p <> 0.
Proof.
rewrite divides_rem_eq; tauto.
Fact df_mexists_size_Z n f : df_size_Z (df_mexists n f) = (Z.of_nat n + df_size_Z f)%Z.
Proof.
rewrite df_size_Z_spec, df_mexists_size, Nat2Z.inj_add, df_size_Z_spec; lia.
End multiple_exists.
Section dio_rel_finite_conj.
Notation "∑" := (msum plus 0).
Definition df_true := proj1_sig dio_rel_True.
Fact df_true_size : df_size df_true = 4.
Proof.
reflexivity.
Fact df_true_spec ν : df_pred df_true ν <-> True.
Proof.
apply (proj2_sig dio_rel_True).
Fixpoint df_mconj n f := match n with | 0 => df_true | S n => f 0 ∧ df_mconj n f⭳ end.
Fact df_mconj_size n f : df_size (df_mconj n f) = 4+n+∑ n (fun i => df_size (f i)).
Proof.
revert f; induction n as [ | n IHn ]; intros f; simpl; auto.
rewrite IHn; ring.
Fact df_mconj_spec n f ν : df_pred (df_mconj n f) ν <-> forall i, i < n -> df_pred (f i) ν.
Proof.
revert f ν; induction n as [ | n IHn ]; intros f v; simpl df_mconj.
+
rewrite df_true_spec; split; auto; intros; lia.
+
rewrite df_pred_conj, IHn; split.
*
intros (? & H2) [ | i ] ?; auto; apply H2; lia.
*
intros H; split; intros; apply H; lia.

Fact dio_rel_cst_sym x n : 𝔻R (fun ν => n = ν x).
Proof.
dio_sym (dio_rel_cst x n).
