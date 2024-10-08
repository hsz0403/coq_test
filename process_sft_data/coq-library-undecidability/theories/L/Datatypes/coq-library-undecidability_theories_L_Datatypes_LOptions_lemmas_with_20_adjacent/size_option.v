From Undecidability.L Require Import Tactics.LTactics Datatypes.LBool Tactics.GenEncode.
From Undecidability.L Require Import Functions.EqBool.
Import L_Notations.
Section Fix_X.
Variable X:Type.
Context {intX : registered X}.
MetaCoq Run (tmGenEncode "option_enc" (option X)).
Hint Resolve option_enc_correct : Lrewrite.
Global Instance term_Some : computableTime' (@Some X) (fun _ _ => (1,tt)).
Proof.
extract constructor.
solverec.
Defined.
End Fix_X.
Hint Resolve option_enc_correct : Lrewrite.
Section option_eqb.
Variable X : Type.
Variable eqb : X -> X -> bool.
Variable spec : forall x y, reflect (x = y) (eqb x y).
Definition option_eqb (A B : option X) := match A,B with | None,None => true | Some x, Some y => eqb x y | _,_ => false end.
End option_eqb.
Section int.
Variable X:Type.
Context {HX : registered X}.
Global Instance term_option_eqb : computableTime' (@option_eqb X) (fun eqb eqbT => (1, fun a _ => (1,fun b _ => (match a,b with Some a, Some b => callTime2 eqbT a b + 10 | _,_ => 8 end,tt)))).
cbn.
Proof.
extract.
solverec.
Global Instance eqbOption f `{eqbClass (X:=X) f}: eqbClass (option_eqb f).
Proof.
intros ? ?.
eapply option_eqb_spec.
all:eauto using eqb_spec.
Global Instance eqbComp_Option `{H:eqbCompT X (R:=HX)}: eqbCompT (option X).
Proof.
evar (c:nat).
exists c.
unfold option_eqb.
unfold enc;cbn.
change (eqb0) with (eqb (X:=X)).
extract.
unfold eqb,eqbTime.
fold (enc (X:=X)).
recRel_prettify2.
easy.
[c]:exact (c__eqbComp X + 6).
all:unfold c.
all:cbn iota beta delta [option_enc].
all: change ((match HX with | @mk_registered _ enc _ _ => enc end)) with (enc (X:=X)).
all:cbn [size].
all: nia.
End int.
Definition isSome {T} (u : option T) := match u with Some _ => true | _ => false end.
Instance term_isSome {T} `{registered T} : computable (@isSome T).
Proof.
extract.

Lemma oenc_correct_some (s: option X) (v : term) : lambda v -> enc s == ext (@Some X) v -> exists s', s = Some s' /\ v = enc s'.
Proof.
intros lam_v H.
unfold ext in H;cbn in H.
unfold extT in H; cbn in H.
redStep in H.
apply unique_normal_forms in H;[|Lproc..].
destruct s;simpl in H.
-
injection H;eauto.
-
Admitted.

Lemma option_eqb_spec A B : reflect (A = B) (option_eqb A B).
Proof using spec.
destruct A, B; try now econstructor.
cbn.
Admitted.

Instance term_isSome {T} `{registered T} : computable (@isSome T).
Proof.
Admitted.

Lemma size_option X `{registered X} (l:option X): size (enc l) = match l with Some x => size (enc x) + 5 | _ => 3 end.
Proof.
change (enc l) with (option_enc l).
destruct l.
all:cbn [option_enc map sumn size].
change ((match H with | @mk_registered _ enc _ _ => enc end x)) with (enc x).
all:lia.
