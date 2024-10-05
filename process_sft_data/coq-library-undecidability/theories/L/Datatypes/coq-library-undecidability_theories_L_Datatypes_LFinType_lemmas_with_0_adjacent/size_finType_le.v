From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L Require Import Datatypes.LNat Functions.EqBool.
From Undecidability.L Require Import UpToC.
Import Nat.
Require Export Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes.
Definition registered_finType `{X : finType} : registered X.
Proof.
eapply (registerAs index).
intros x y H.
now apply injective_index.
Defined.
Definition finType_eqb {X:finType} (x y : X) := Nat.eqb (index x) (index y).
Section finType_eqb.
Local Existing Instance registered_finType.
Global Instance term_index (F:finType): computableTime' (@index F) (fun _ _=> (1, tt)).
Proof.
apply cast_computableTime.
Local Instance eqbFinType_inst (X:finType): eqbClass finType_eqb (X:=X).
Proof.
intros ? ?.
eapply finType_eqb_reflect.
Import Nat.
Global Instance eqbFinType (X:finType): eqbCompT X.
Proof.
evar (c:nat).
exists c.
unfold finType_eqb.
unfold enc;cbn.
extract.
unfold eqbTime.
solverec.
[c]:exact (c__eqbComp nat + 8).
rewrite !size_nat_enc.
all:unfold c, c__natsizeO;try nia.
End finType_eqb.

Lemma size_finType_le (X:finType) (x:X): size (enc (registered := registered_finType) x) <= length (elem X) * 4.
Proof.
rewrite enc_finType_eq,size_nat_enc.
specialize (index_le x).
unfold c__natsizeS, c__natsizeO.
lia.
