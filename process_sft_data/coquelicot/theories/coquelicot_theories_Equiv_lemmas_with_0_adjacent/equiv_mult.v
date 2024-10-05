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

Lemma equiv_mult : forall {T} {F : (T -> Prop) -> Prop} {FF : Filter F} (f1 f2 g1 g2 : T -> R), is_equiv F f1 g1 -> is_equiv F f2 g2 -> is_equiv F (fun x => f1 x * f2 x) (fun x => g1 x * g2 x).
Proof.
intros T F FF f1 f2 g1 g2 H1 H2.
case: (equiv_carac_0 _ _ H1) => {H1} o1 [H1 Ho1].
case: (equiv_carac_0 _ _ H2) => {H2} o2 [H2 Ho2].
apply equiv_carac_1 with (fun x => o1 x * g2 x + g1 x * o2 x + o1 x * o2 x).
move => x ; rewrite H1 H2 /plus /= ; ring.
repeat apply @domin_plus => //.
by apply domin_mult_r.
by apply domin_mult_l.
by apply domin_mult.
