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

Lemma ren_poly_type_id' {ξ t} : (forall x, ξ x = x) -> ren_poly_type ξ t = t.
Proof.
rewrite -[RHS]ren_poly_type_id => ?.
Admitted.

Fact ren_as_subst_poly_type {ξ t} : ren_poly_type ξ t = subst_poly_type (ξ >> poly_var) t.
Proof.
Admitted.

Lemma iter_scons {X: Type} {x: X} {f: nat -> X} {n m: nat} : Nat.iter n (scons x) f (n + m) = f m.
Proof.
elim: n m f; first done.
move=> n IH m f /=.
Admitted.

Lemma iter_scons_ge {X: Type} {f: nat -> X} {n x m} : n <= m -> Nat.iter n (scons x) f m = f (m - n).
Proof.
move=> ?.
have {1}->: m = n + (m - n) by lia.
Admitted.

Lemma iter_scons_lt {X: Type} {x: X} {f: nat -> X} {n m: nat} : m < n -> Nat.iter n (scons x) f m = x.
Proof.
elim: n m f; first by lia.
move=> n IH [|m] f /= ?; first done.
Admitted.

Lemma iter_up_poly_type_poly_type {n σ x} : Nat.iter n up_poly_type_poly_type σ (n + x) = ren_poly_type (Nat.add n) (σ x).
Proof.
elim: n x σ; first by move=> ? ?; rewrite ren_poly_type_id.
move=> n IH x σ /=.
Admitted.

Lemma iter_up_poly_type_poly_type_lt {n σ x} : x < n -> Nat.iter n up_poly_type_poly_type σ x = poly_var x.
Proof.
elim: n x σ; first by lia.
move=> n IH [|x] σ /= ?; first done.
Admitted.

Lemma iter_up_poly_type_poly_type_ge {n σ x} : x >= n -> Nat.iter n up_poly_type_poly_type σ x = ren_poly_type (Nat.add n) (σ (x - n)).
Proof.
move=> ?.
have {1}->: x = n + (x - n) by lia.
Admitted.

Lemma allfv_poly_type_impl {P1 P2: nat -> Prop} {t}: (forall x, P1 x -> P2 x) -> allfv_poly_type P1 t -> allfv_poly_type P2 t.
Proof.
elim: t P1 P2.
-
move=> >.
by apply.
-
by move=> ? IH1 ? IH2 > /= /copy [/IH1 {}IH1 /IH2 {}IH2] [/IH1 ? /IH2 ?].
-
move=> ? IH > H /=.
apply: IH.
Admitted.

Lemma allfv_poly_type_allfv_poly_type_impl {P1 P2: nat -> Prop} {t}: allfv_poly_type (fun x => P1 x -> P2 x) t -> allfv_poly_type P1 t -> allfv_poly_type P2 t.
Proof.
elim: t P1 P2.
-
done.
-
move=> ? IH1 ? IH2 > /= [/IH1 {}IH1 /IH2 {}IH2] [/IH1 ? /IH2 ?].
by constructor.
-
move=> ? IH > /= H.
apply: IH.
apply: allfv_poly_type_impl H.
Admitted.

Lemma ext_allfv_poly_type {P1 P2 t}: (forall x, P1 x <-> P2 x) -> allfv_poly_type P1 t <-> allfv_poly_type P2 t.
Proof.
move=> H.
Admitted.

Lemma ext_allfv_poly_type_allfv_poly_type {P1 P2 t}: allfv_poly_type (fun x => P1 x <-> P2 x) t -> allfv_poly_type P1 t <-> allfv_poly_type P2 t.
Proof.
move=> H.
Admitted.

Lemma allfv_poly_type_many_poly_absI {P n t} : allfv_poly_type (Nat.iter n (scons True) P) t -> allfv_poly_type P (many_poly_abs n t).
Proof.
elim: n P; first done.
move=> n IH P.
Admitted.

Lemma allfv_poly_type_many_poly_arrI {P ss x} : Forall (allfv_poly_type P) ss -> P x -> allfv_poly_type P (many_poly_arr ss (poly_var x)).
Proof.
elim: ss; first done.
move=> > IH /Forall_consP [? /IH {}IH] /IH ?.
Admitted.

Lemma ext_ren_poly_type_allfv_poly_type {t ξ ξ'} : allfv_poly_type (fun x => ξ x = ξ' x) t -> ren_poly_type ξ t = ren_poly_type ξ' t.
Proof.
move=> H.
rewrite ?ren_as_subst_poly_type.
apply: ext_subst_poly_type_allfv_poly_type.
apply: allfv_poly_type_impl H => ?.
Admitted.

Lemma allfv_poly_type_ren_poly_type {P ξ t} : allfv_poly_type P (ren_poly_type ξ t) <-> (allfv_poly_type (ξ >> P) t).
Proof.
elim: t ξ P.
-
done.
-
by move=> /= ? + ? + ? ? => -> ->.
-
move=> ? /= IH ? ?.
rewrite IH.
apply: ext_allfv_poly_type.
rewrite /scons /funcomp.
Admitted.

Lemma allfv_poly_type_subst_poly_type {P σ t} : allfv_poly_type P (subst_poly_type σ t) <-> (allfv_poly_type (σ >> allfv_poly_type P) t).
Proof.
elim: t σ P.
-
done.
-
by move=> /= ? + ? + ? ? => -> ->.
-
move=> ? /= IH ? ?.
rewrite IH.
apply: ext_allfv_poly_type.
rewrite /scons /funcomp.
case; first done.
move=> x.
rewrite allfv_poly_type_ren_poly_type.
Admitted.

Lemma allfv_poly_type_many_poly_abs {P n t} : allfv_poly_type P (many_poly_abs n t) = allfv_poly_type (Nat.iter n (scons True) P) t.
Proof.
Admitted.

Lemma allfv_poly_type_TrueI {p: nat -> Prop} {t} : (forall x, p x) -> allfv_poly_type p t.
Proof.
move=> Hp.
elim: t; [done | done |].
move=> /= ?.
apply: allfv_poly_type_impl.
case; first done.
move=> *.
Admitted.

Lemma ren_poly_type_allfv_id {ξ t} : (allfv_poly_type (fun x => ξ x = x) t) -> ren_poly_type ξ t = t.
Proof.
rewrite -[RHS]ren_poly_type_id => ?.
Admitted.

Lemma ren_poly_type_closed_id {ξ t} : allfv_poly_type (fun=> False) t -> ren_poly_type ξ t = t.
Proof.
move=> H.
apply: ren_poly_type_allfv_id.
Admitted.

Lemma poly_var_boundP t : allfv_poly_type (gt (poly_var_bound t)) t.
Proof.
elim: t.
-
move=> /=.
by lia.
-
move=> ? IH1 ? IH2 /=.
by constructor; [move: IH1 | move: IH2]; apply: allfv_poly_type_impl; lia.
-
move=> ? /=.
apply: allfv_poly_type_impl.
Admitted.

Lemma iter_up_ren {n ξ x} : Nat.iter n up_ren ξ (n + x) = n + ξ x.
Proof.
elim: n x ξ; first done.
move=> n IH x ξ /=.
rewrite /funcomp IH.
Admitted.

Lemma iter_up_ren_lt {n ξ x} : x < n -> Nat.iter n up_ren ξ x = x.
Proof.
elim: n x ξ; first by lia.
move=> n IH [|x] ξ /= ?; first done.
Admitted.

Lemma iter_up_ren_ge {n ξ x} : n <= x -> Nat.iter n up_ren ξ x = n + ξ (x-n).
Proof.
move=> ?.
have {1}->: x = n + (x - n) by lia.
Admitted.

Lemma iter_up_ren_ge' {ξ n n' x}: x >= n -> Nat.iter (n + n') up_ren ξ x = n + Nat.iter n' up_ren ξ (x - n).
Proof.
move=> ?.
have [?|?] : x < n + n' \/ n + n' <= x by lia.
-
rewrite ?iter_up_ren_lt; by lia.
-
have ? : ξ (x - (n + n')) = ξ (x - n - n') by congr ξ; lia.
Admitted.

Lemma iter_up_ren_add {n m x}: Nat.iter n up_ren (Nat.add m) x = x + (Nat.iter n (locked up_ren) (Nat.add m) x - x).
Proof.
rewrite -lock.
have [?|->] : x < n \/ x = n + (x - n) by lia.
-
rewrite iter_up_ren_lt; by lia.
-
rewrite iter_up_ren.
Admitted.

Lemma iter_up_ren_iter_up_ren {n ξ1 ξ2 x} : Nat.iter n up_ren ξ1 (Nat.iter n up_ren ξ2 x) = Nat.iter n up_ren (ξ2 >> ξ1) x.
Proof.
have [?|->] : x < n \/ x = n + (x - n) by lia.
-
rewrite [Nat.iter _ _ ξ2 x]iter_up_ren_lt; first done.
rewrite iter_up_ren_lt; first done.
by rewrite iter_up_ren_lt; first done.
-
Admitted.

Lemma ren_poly_type_poly_var_bound {ξ n t} : poly_var_bound t <= n -> ren_poly_type (Nat.iter n up_ren ξ) t = t.
Proof.
move=> H.
apply: ren_poly_type_allfv_id.
apply: allfv_poly_type_impl (poly_var_boundP t) => ? ?.
apply: iter_up_ren_lt.
Admitted.

Lemma subst_poly_type_map_seq {f n t} : poly_var_bound t <= n -> subst_poly_type (fold_right scons poly_var (map f (seq 0 n))) t = subst_poly_type f t.
Proof.
move=> H.
apply: ext_subst_poly_type_allfv_poly_type.
apply: allfv_poly_type_impl (poly_var_boundP t) => x ?.
apply: fold_right_map_seq.
Admitted.

Lemma map_ren_poly_type_id {Gamma} : map (ren_poly_type id) Gamma = Gamma.
Proof.
under map_ext => ? do rewrite ren_poly_type_id.
Admitted.

Lemma many_poly_abs_many_poly_abs {n m t} : many_poly_abs n (many_poly_abs m t) = many_poly_abs (n + m) t.
Proof.
Admitted.

Lemma many_poly_abs_eqE {n s t} : many_poly_abs n s = many_poly_abs n t -> s = t.
Proof.
Admitted.

Lemma many_poly_abs_eqE' {n1 n2 s t} : many_poly_abs n1 s = many_poly_abs n2 t -> match s, t with | poly_abs _, _ | _, poly_abs _ => True | _, _ => n1 = n2 /\ s = t end.
Proof.
elim: n1 n2.
-
case.
+
move=> /= ->.
by case: t.
+
by move=> ? /= ->.
-
move=> n IH.
case.
+
move=> /= <-.
clear.
by case: s.
+
move=> ? [/IH].
clear.
Admitted.

Lemma ext_subst_poly_type_allfv_poly_type {t σ σ'} : allfv_poly_type (fun x => σ x = σ' x) t -> subst_poly_type σ t = subst_poly_type σ' t.
Proof.
elim: t σ σ'.
-
by move=> > /= ->.
-
by move=> ? IH1 ? IH2 > /= [/IH1 -> /IH2 ->].
-
move=> ? IH > /= H.
congr poly_abs.
apply: IH.
apply: iffLR H.
apply: ext_allfv_poly_type.
case; first done.
move=> x /=.
rewrite /funcomp.
constructor; first by move=> ->.
move=> /(congr1 (ren_poly_type Nat.pred)).
by rewrite ?poly_type_norm ?ren_poly_type_id.
