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

Lemma eqbTime_le_r X (R : registered X) (eqb : X -> X -> bool) (H : eqbClass eqb) (eqbCompT : eqbCompT X) x n': eqbTime (X:=X) n' x <= x * c__eqbComp X.
Proof.
unfold eqbTime.
rewrite Nat.le_min_r.
easy.
