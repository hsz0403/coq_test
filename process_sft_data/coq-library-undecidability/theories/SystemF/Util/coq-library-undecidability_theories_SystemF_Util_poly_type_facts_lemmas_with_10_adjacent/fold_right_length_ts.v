Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax Undecidability.SystemF.Autosubst.unscoped.
Import UnscopedNotations.
Require Import Undecidability.SystemF.Util.Facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Goal Selector "!".
Fixpoint allfv_poly_type (p: nat -> Prop) (t: poly_type) := match t with | poly_var x => p x | poly_arr s t => allfv_poly_type p s /\ allfv_poly_type p t | poly_abs t => allfv_poly_type (scons True p) t end.
Fixpoint is_simple (t: poly_type) := match t with | poly_var _ => True | poly_arr s t => is_simple s /\ is_simple t | poly_abs _ => False end.
Definition many_poly_arr (arguments: list poly_type) (target: poly_type) := fold_right poly_arr target arguments.
Definition many_poly_abs (n: nat) (t: poly_type) := Nat.iter n poly_abs t.
Fact subst_poly_type_many_poly_abs {σ n target} : subst_poly_type σ (many_poly_abs n target) = many_poly_abs n (subst_poly_type (Nat.iter n up_poly_type_poly_type σ) target).
Proof.
elim: n σ; first done.
move=> n IH σ /=.
congr poly_abs.
by rewrite IH iter_last.
Fact ren_poly_type_many_poly_abs {ξ n target} : ren_poly_type ξ (many_poly_abs n target) = many_poly_abs n (ren_poly_type (Nat.iter n up_ren ξ) target).
Proof.
elim: n ξ; first done.
move=> n IH ξ /=.
congr poly_abs.
by rewrite IH iter_last.
Fact subst_poly_type_many_poly_arr {σ args target} : subst_poly_type σ (many_poly_arr args target) = many_poly_arr (map (subst_poly_type σ) args) (subst_poly_type σ target).
Proof.
elim: args; first done.
move=> s args IH /=.
congr poly_arr.
by apply: IH.
Fixpoint last_poly_var (t: poly_type) : option nat := match t with | poly_var x => Some x | poly_arr _ t => last_poly_var t | poly_abs t => if last_poly_var t is Some (S x) then Some x else None end.
Fixpoint parameters_poly_arr (t: poly_type) : list poly_type := match t with | poly_var x => [] | poly_arr s t => s :: parameters_poly_arr t | poly_abs t => [] end.
Fact up_ren_id {x} : up_ren id x = x.
Proof.
by case x.
Fact upRen_poly_type_poly_type_id {t}: upRen_poly_type_poly_type id t = t.
Proof.
by case: t.
Definition poly_type_norm := (renComp_poly_type, compComp_poly_type, renRen_poly_type, compRen_poly_type).
Fact subst_poly_type_poly_var {t} : subst_poly_type poly_var t = t.
Proof.
by rewrite idSubst_poly_type.
Fact subst_poly_type_poly_var' {σ t} : (forall x, σ x = poly_var x) -> subst_poly_type σ t = t.
Proof.
move=> ?.
by apply: idSubst_poly_type.
Fact map_subst_poly_type_poly_var {Gamma} : map (subst_poly_type poly_var) Gamma = Gamma.
Proof.
apply: map_id' => ?.
by rewrite subst_poly_type_poly_var.
Fact ren_poly_type_id {t}: ren_poly_type id t = t.
Proof.
rewrite -[RHS]subst_poly_type_poly_var.
by apply: rinst_inst_poly_type.
Fact ren_as_subst_poly_type {ξ t} : ren_poly_type ξ t = subst_poly_type (ξ >> poly_var) t.
Proof.
by apply: rinst_inst_poly_type.
Definition ext_poly_type := ext_poly_type.
Fixpoint poly_var_bound (t: poly_type) : nat := match t with | poly_var x => 1 + x | poly_arr s t => 1 + poly_var_bound s + poly_var_bound t | poly_abs p => 1 + poly_var_bound p end.
Definition is_poly_abs (t: poly_type) := if t is poly_abs _ then True else False.
Definition fresh_in (x: nat) (t: poly_type) := allfv_poly_type (fun y => x <> y) t.
Fixpoint fresh_inb (x: nat) (t: poly_type) := match t with | poly_var y => if PeanoNat.Nat.eq_dec x y then false else true | poly_arr s t => fresh_inb x s && fresh_inb x t | poly_abs t => fresh_inb (1+x) t end.

Fact subst_poly_type_many_poly_abs {σ n target} : subst_poly_type σ (many_poly_abs n target) = many_poly_abs n (subst_poly_type (Nat.iter n up_poly_type_poly_type σ) target).
Proof.
elim: n σ; first done.
move=> n IH σ /=.
congr poly_abs.
Admitted.

Fact ren_poly_type_many_poly_abs {ξ n target} : ren_poly_type ξ (many_poly_abs n target) = many_poly_abs n (ren_poly_type (Nat.iter n up_ren ξ) target).
Proof.
elim: n ξ; first done.
move=> n IH ξ /=.
congr poly_abs.
Admitted.

Fact subst_poly_type_many_poly_arr {σ args target} : subst_poly_type σ (many_poly_arr args target) = many_poly_arr (map (subst_poly_type σ) args) (subst_poly_type σ target).
Proof.
elim: args; first done.
move=> s args IH /=.
congr poly_arr.
Admitted.

Lemma parameters_many_poly_arr {ss x} : parameters_poly_arr (many_poly_arr ss (poly_var x)) = ss.
Proof.
elim: ss; first done.
move=> /=.
Admitted.

Lemma fold_right_length_ts_lt {σ: nat -> poly_type} {ts x} : x < length ts -> fold_right scons σ ts x = nth x ts (poly_var 0).
Proof.
elim: ts x σ; [ by move=> /=; lia |].
Admitted.

Lemma fold_right_length_ts_ge {σ : nat -> poly_type} {ts x} : length ts <= x -> fold_right scons σ ts x = σ (x - length ts).
Proof.
move=> ?.
have {1}->: x = length ts + (x - length ts) by lia.
Admitted.

Lemma fold_right_map_seq {f: nat -> poly_type} {x n} : x < n -> fold_right scons poly_var (map f (seq 0 n)) x = f x.
Proof.
move=> ?.
rewrite fold_right_length_ts_lt; first by rewrite map_length seq_length; lia.
rewrite (nth_indep _ _ (f 0)); first by rewrite map_length seq_length; lia.
Admitted.

Fact up_ren_id {x} : up_ren id x = x.
Proof.
Admitted.

Fact upRen_poly_type_poly_type_id {t}: upRen_poly_type_poly_type id t = t.
Proof.
Admitted.

Lemma up_poly_type_poly_type_poly_var {x} : up_poly_type_poly_type poly_var x = poly_var x.
Proof.
Admitted.

Fact subst_poly_type_poly_var {t} : subst_poly_type poly_var t = t.
Proof.
Admitted.

Fact subst_poly_type_poly_var' {σ t} : (forall x, σ x = poly_var x) -> subst_poly_type σ t = t.
Proof.
move=> ?.
Admitted.

Fact map_subst_poly_type_poly_var {Gamma} : map (subst_poly_type poly_var) Gamma = Gamma.
Proof.
apply: map_id' => ?.
Admitted.

Fact ren_poly_type_id {t}: ren_poly_type id t = t.
Proof.
rewrite -[RHS]subst_poly_type_poly_var.
Admitted.

Lemma fold_right_length_ts {σ: nat -> poly_type} {ts x} : fold_right scons σ ts (length ts + x) = σ x.
Proof.
elim: ts σ; [done | by move=> t ts + σ; apply].
