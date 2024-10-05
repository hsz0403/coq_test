Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Rbar Rcomplements Hierarchy.
Definition is_domin {T} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} (F : (T -> Prop) -> Prop) (f : T -> U) (g : T -> V) := forall eps : posreal, F (fun x => norm (g x) <= eps * norm (f x)).
Definition is_equiv {T} {K : AbsRing} {V : NormedModule K} (F : (T -> Prop) -> Prop) (f g : T -> V) := is_domin F g (fun x => minus (g x) (f x)).
Section Equiv.
Context {T : Type} {K : AbsRing} {V : NormedModule K}.
End Equiv.
Section Domin.
Context {T : Type} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv}.
End Domin.
Section Equiv_VS.
Context {T : Type} {K : AbsRing} {V : NormedModule K}.
End Equiv_VS.
Section Domin_comp.
Context {T1 T2 : Type} {Ku Kv : AbsRing} {U : NormedModule Ku} {V : NormedModule Kv} (F : (T1 -> Prop) -> Prop) {FF : Filter F} (G : (T2 -> Prop) -> Prop) {FG : Filter G}.
End Domin_comp.

Lemma domin_mult : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f1 f2 g1 g2 : T -> R), is_domin F f1 g1 -> is_domin F f2 g2 -> is_domin F (fun x => f1 x * f2 x) (fun x => g1 x * g2 x).
Proof.
intros T F FF f1 f2 g1 g2 H1 H2 eps.
move: (H1 (mkposreal _ (sqrt_lt_R0 _ (cond_pos eps)))) (H2 (mkposreal _ (sqrt_lt_R0 _ (cond_pos eps)))) => {H1 H2} /= H1 H2.
generalize (filter_and _ _ H1 H2) => {H1 H2}.
apply filter_imp => x [H1 H2].
rewrite /norm /= /abs /= ?Rabs_mult.
rewrite -(sqrt_sqrt _ (Rlt_le _ _ (cond_pos eps))).
replace (sqrt eps * sqrt eps * (Rabs (f1 x) * Rabs (f2 x))) with ((sqrt eps * Rabs (f1 x))*(sqrt eps * Rabs (f2 x))) by ring.
apply Rmult_le_compat.
by apply Rabs_pos.
by apply Rabs_pos.
by apply H1.
by apply H2.
