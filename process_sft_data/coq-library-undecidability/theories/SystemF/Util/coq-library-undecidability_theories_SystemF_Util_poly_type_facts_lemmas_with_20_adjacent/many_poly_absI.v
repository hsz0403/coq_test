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

Lemma many_poly_abs_eqE'' {n1 t1 n2 t2} : many_poly_abs n1 t1 = many_poly_abs n2 t2 -> not (is_poly_abs t2) -> exists n3, t1 = many_poly_abs n3 t2 /\ n2 = n1 + n3.
Proof.
elim: n2 n1.
-
move=> [|?].
+
move=> /= <- _.
by exists 0.
+
by move=> /= <- /=.
-
move=> n1 IH [|n2].
+
move=> /= -> _.
by exists (1+n1).
+
move=> [/IH H] /H [n3] [-> ->].
Admitted.

Lemma many_poly_abs_poly_var_eq_subst_poly_typeE {σ n x t}: many_poly_abs n (poly_var (n+x)) = subst_poly_type σ t -> exists i m y, n = i + m /\ t = many_poly_abs m (poly_var (m+y)).
Proof.
have [n' [t' [-> +]]] := many_poly_absI t.
case: t'.
-
move=> y _.
rewrite subst_poly_type_many_poly_abs /=.
have [?|->] : y < n' \/ y = n' + (y - n') by lia.
+
rewrite iter_up_poly_type_poly_type_lt; first done.
move=> <-.
by exists 0, n, x.
+
move=> /esym /many_poly_abs_eqE'' /(_ ltac:(done)).
move=> [n''] [? ->].
exists n'', n', (y - n').
constructor; [by lia | done].
-
move=> ? ? _.
rewrite subst_poly_type_many_poly_abs /=.
by move=> /many_poly_abs_eqE' [].
-
Admitted.

Lemma many_poly_abs_poly_arr_eq_subst_poly_typeE {σ n x t}: many_poly_abs n (poly_arr (poly_var (n+x)) (poly_var (n+x))) = subst_poly_type σ t -> (exists m y, t = many_poly_abs m (poly_var (m+y))) \/ (exists m y1 y2, t = many_poly_abs m (poly_arr (poly_var (m+y1)) (poly_var (m+y2)))).
Proof.
have [n' [t' [-> +]]] := many_poly_absI t.
case: t'.
-
move=> y _.
rewrite subst_poly_type_many_poly_abs /=.
have [?|->] : y < n' \/ y = n' + (y - n') by lia.
+
rewrite iter_up_poly_type_poly_type_lt; first done.
move=> <-.
right.
by exists n, x, x.
+
move=> ?.
left.
by exists n', (y - n').
-
move=> s'' t'' _.
rewrite subst_poly_type_many_poly_abs /=.
move=> /many_poly_abs_eqE' [<-] [].
case: s''; [ | done | done].
case: t''; [ | done | done].
move=> y1 y2 /=.
have [?|->] : y1 < n \/ y1 = n + (y1 - n) by lia.
+
move=> _.
rewrite iter_up_poly_type_poly_type_lt; first done.
move=> [].
by lia.
+
have [?|->] : y2 < n \/ y2 = n + (y2 - n) by lia.
*
move=> + _.
rewrite iter_up_poly_type_poly_type_lt; first done.
move=> [].
by lia.
*
move=> _ _.
right.
by exists n, (y2-n), (y1-n).
-
Admitted.

Lemma fresh_inP {x t} : reflect (fresh_in x t) (fresh_inb x t).
Proof.
elim: t x.
-
move=> n x.
rewrite /=.
case: (PeanoNat.Nat.eq_dec _ _).
+
move=> /= ->.
by constructor.
+
move=> /= ?.
by constructor.
-
move=> ? IH1 ? IH2 x /=.
rewrite /fresh_in /= -?/(fresh_in _ _).
apply /introP; rewrite (rwP (IH1 x)) (rwP (IH2 x)).
+
by case: (fresh_inb _ _); case (fresh_inb _ _).
+
case: (fresh_inb _ _); case (fresh_inb _ _); by move=> ? [? ?].
-
move=> t IH x.
rewrite /fresh_in /= -?/(fresh_in _ _).
apply /introP.
+
rewrite -(rwP (IH (S x))).
apply: allfv_poly_type_impl.
case; [done | by move=> /= *; lia].
+
have := (rwP (IH (S x))).
case: (fresh_inb (S x) t); first done.
move=> H _ H'.
suff: false by done.
apply /H.
apply: allfv_poly_type_impl H'.
Admitted.

Lemma fresh_in_many_poly_absI {x n t} : fresh_in (n+x) t -> fresh_in x (many_poly_abs n t).
Proof.
move=> H.
apply /allfv_poly_type_many_poly_absI.
apply: allfv_poly_type_impl H => y ?.
have [?|?] : y < n \/ n <= y by lia.
-
by rewrite iter_scons_lt.
-
Admitted.

Lemma fresh_in_many_poly_arrI {x ss y} : Forall (fresh_in x) ss -> x <> y -> fresh_in x (many_poly_arr ss (poly_var y)).
Proof.
move=> *.
Admitted.

Lemma many_poly_absI t : exists n s, t = many_poly_abs n s /\ not (is_poly_abs s).
Proof.
elim: t.
-
move=> >.
exists 0.
eexists.
by constructor.
-
move=> >.
exists 0.
eexists.
by constructor.
-
move=> t [n] [s] [-> ?].
exists (1+n).
by eexists.
