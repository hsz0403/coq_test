From Undecidability.L Require Import L Tactics.LTactics LBool.
Class eqbClass X (eqb : X -> X -> bool): Type := _eqb_spec : forall (x y:X), reflect (x=y) (eqb x y).
Hint Mode eqbClass + -: typeclass_instances.
Definition eqb X eqb `{H:eqbClass (X:=X) eqb} := eqb.
Arguments eqb {_ _ _}: simpl never.
Instance eqbBool_inst : eqbClass Bool.eqb.
Proof.
intros ? ?.
eapply iff_reflect.
rewrite eqb_true_iff.
reflexivity.
Class eqbCompT X {R:registered X} eqb {H:eqbClass (X:=X) eqb} := { c__eqbComp :nat; eqbTime x y:= min x y* c__eqbComp; comp_eqb : computableTime' eqb (fun x _ =>(5,fun y _ => (eqbTime (size (enc x)) (size (enc y)),tt))) }.
Arguments eqbCompT _ {_ _ _}.
Arguments c__eqbComp _ {_ _ _ _}.
Hint Mode eqbCompT + - - -: typeclass_instances.
Existing Instance comp_eqb.
Instance eqbComp_bool : eqbCompT bool.
Proof.
evar (c:nat).
exists c.
unfold Bool.eqb.
unfold enc;cbn.
extract.
solverec.
[c]:exact 3.
all:unfold c;try lia.

Lemma eqb_spec {X} {f : X -> X -> bool} {_:eqbClass f}: forall (x y:X), reflect (x=y) (eqb x y).
Proof.
intros.
Admitted.

Instance eqbBool_inst : eqbClass Bool.eqb.
Proof.
intros ? ?.
eapply iff_reflect.
rewrite eqb_true_iff.
Admitted.

Lemma dec_reflect_remove {P Y} (d:dec P) b (H:reflect P b) (y y' : Y): (if d then y else y') = (if b then y else y').
Proof.
Admitted.

Instance eqbComp_bool : eqbCompT bool.
Proof.
evar (c:nat).
exists c.
unfold Bool.eqb.
unfold enc;cbn.
extract.
solverec.
[c]:exact 3.
Admitted.

Lemma eqbTime_le_l X {R : registered X} (eqb : X -> X -> bool) {H : eqbClass eqb} {H' : eqbCompT X} x n': eqbTime (X:=X) x n' <= x * c__eqbComp X.
Proof.
unfold eqbTime.
rewrite Nat.le_min_l.
Admitted.

Lemma eqbTime_le_r X (R : registered X) (eqb : X -> X -> bool) (H : eqbClass eqb) (eqbCompT : eqbCompT X) x n': eqbTime (X:=X) n' x <= x * c__eqbComp X.
Proof.
unfold eqbTime.
rewrite Nat.le_min_r.
Admitted.

Lemma eqDec_remove {X Y eqb} {H:eqbClass (X:=X) eqb} x x' (d:dec (x=x')) (a b : Y): (if d then a else b) = (if eqb x x' then a else b).
Proof.
apply dec_reflect_remove.
eapply eqb_spec.
