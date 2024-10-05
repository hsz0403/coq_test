From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Domain Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL Require Import Actions Injection Process Always.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Structure prog (W : world) A (this : nid) := Prog { set_of : proc this W A -> Prop; (* Unifinshed is a bottom element that should be present *) _ : set_of Unfinished }.
Section Programs.
Variable this : nid.
Variable W : world.
Variable A : Type.
Notation coherent := (Coh W).
Arguments Prog [W A].
Arguments Prog [W A this].
Coercion set_of : prog >-> Funclass.
Canonical prog_PredType W A := mkPredType (fun p => @set_of W A this p).
Definition pre := state -> Prop.
Definition post A := state -> A -> state -> Prop.
Definition cont A := A -> state -> Prop.
Definition spec A := prod pre (post A).
Definition has_spec (s : spec A) := [Pred T : prog W A this | forall i t, s.1 i -> i \In Coh W -> t \In T -> after i t (s.2 i)].
End Programs.
Module DTbin.
Section DTbin.
Variable this : nid.
Structure DTbin (W : world) A (s : spec A) := DTbin_make { prog_of : prog W A this; _ : prog_of \In has_spec this W s}.
End DTbin.
End DTbin.
Notation DTbin := DTbin.DTbin.
Notation DTbin_make := DTbin.DTbin_make.
Coercion DTbin.prog_of : DTbin >-> prog.
Section Specs.
Variable this : nid.
Inductive DT (W: world) A := with_spec (s : spec A) of DTbin this W s.
Definition spec_of W A (e : DT W A) := let: with_spec s _ := e in s.
Definition pre_of W A := fun e : DT W A => (spec_of e).1.
Definition post_of W A := fun e : DT W A => (spec_of e).2.
Definition code_of (W : world) A (e : DT W A) := let: with_spec _ c := e return DTbin this W (spec_of e) in c.
Arguments pre_of [W A].
Arguments post_of [W A].
Arguments with_spec [W A].
Prenex Implicits pre_of post_of.
Coercion with_spec : DTbin >-> DT.
Definition verify (W : world) A (i : state) (e : DT W A) r := i \In Coh W -> forall p, p \In DTbin.prog_of (code_of e) -> after i p r.
End Specs.
Module DTLattice.
Section DTLattice.
Variable this : nid.
Variable W : world.
Variables (A : Type) (s : spec A).
Notation prog A := (@prog W A this).
Notation DTbin s := (@DTbin this W A s).
Definition leq (e1 e2 : DTbin s) := set_of (DTbin.prog_of e1) <== set_of (DTbin.prog_of e2).
Definition bot_set t := t = @Unfinished this W A.
Definition bot_prg := @Prog _ _ _ bot_set (erefl _).
Definition bot := DTbin_make bot_spec.
Definition sup_set (es : Pred (DTbin s)) t := t = Unfinished \/ exists e : DTbin s, t \In DTbin.prog_of e /\ e \In es.
Definition sup_prog es := @Prog _ _ _ (sup_set es) (or_introl (erefl _)).
Definition sup es := DTbin_make (@sup_spec es).
End DTLattice.
Module Exports.
Section Exports.
Variable this : nid.
Variable W : world.
Variables (A : Type) (s : spec A).
Definition stPosetMixin := PosetMixin (@leq_refl this W A s) (@leq_asym this W A s) (@leq_trans this W A s).
Canonical stPoset := Eval hnf in Poset (@DTbin this W A s) stPosetMixin.
Definition stLatticeMixin := LatticeMixin (@sup_supB this W A s) (@sup_supL this W A s).
Canonical stLattice := Eval hnf in Lattice (@DTbin this W A s) stLatticeMixin.
End Exports.
End Exports.
End DTLattice.
Export DTLattice.Exports.
Section Fix.
Variable this : nid.
Variable W : world.
Variables (A : Type) (B : A -> Type) (s : forall x, spec (B x)).
Notation tp := (forall x, DTbin this W (s x)).
Notation lat := (dfunLattice (fun x => [lattice of DTbin this W (s x)])).
Variable (f : tp -> tp).
Definition f' (e : lat) := sup [Pred t : lat | exists e', e' <== e /\ t = f e'].
Definition ffix : tp := tarski_lfp f'.
End Fix.
Section Return.
Variable this : nid.
Variable W : world.
Variables (A : Type) (x : A).
Definition ret_set t := t = Unfinished \/ t = @Ret this W A x.
Definition ret_prog := @Prog _ _ _ ret_set (or_introl (erefl _)).
Definition ret_s : spec A := (fun i => True, fun i y m => network_rely W this i m /\ y = x).
Definition ret := with_spec (DTbin_make ret_has_spec).
End Return.
Section Act.
Variable this : nid.
Variable W : world.
Variables (A : Type) (x : A).
Variable a : action W A this.
Definition act_set t := t = Unfinished \/ t = @Act this W A a.
Definition act_prog := @Prog _ _ _ act_set (or_introl (erefl _)).
Definition act_s : spec A := (fun i => forall j, network_rely W this i j -> a_safe a j, fun i y m => exists j k, [/\ network_rely W this i j, exists (S: a_safe a j), a_step S k y & network_rely W this k m]).
Definition act := with_spec (DTbin_make act_has_spec).
End Act.
Section Bind.
Variable this : nid.
Variable W : world.
Variables (A B : Type).
Section Prog.
Variables (T : prog W A this) (K : A -> prog W B this).
Definition bnd_set t := t = Unfinished \/ exists t', t \In pcat t' K /\ t' \In T.
Definition bnd_prog := @Prog _ _ _ bnd_set (or_introl (erefl _)).
End Prog.
Variables (e1 : DT this W A) (e2 : A -> DT this W B).
Notation s1 := (spec_of e1).
Notation s2 := (fun x => spec_of (e2 x)).
Definition bind_s : spec B := (fun i => s1.1 i /\ forall x s, s1.2 i x s -> (s2 x).1 s, fun i y m => exists x s, s1.2 i x s /\ (s2 x).2 s y m).
Definition bind := with_spec (DTbin_make bind_has_spec).
End Bind.
Section Inject.
Variables (this : nid) (V W : world) (K : hooks) (A : Type) (w : injects V W K).
Variable (e : DT this V A).
Notation W2 := (inj_ext w).
Notation s := (spec_of e).
Section Prog.
Variable T : prog V A this.
Definition inject_set t := t = Unfinished \/ exists t', t' \In T /\ t = Inject w t'.
Definition inject_prog := @Prog _ _ _ inject_set (or_introl (erefl _)).
End Prog.
Definition inject_s : spec A := (fun i => exists i1 i2, i = i1 \+ i2 /\ i1 \In Coh V /\ s.1 i1, fun i y m => forall i1 i2, i = i1 \+ i2 -> i1 \In Coh V -> exists m1 m2, [/\ m = m1 \+ m2, s.2 i1 y m1 & network_rely W2 this i2 m2]).
Definition inject := with_spec (DTbin_make inject_has_spec).
End Inject.
From DiSeL Require Import InductiveInv.
Section InductiveInv.
Variable pr : protocol.
Notation l := (plab pr).
Notation coh := (coh pr).
Variable I : dstatelet -> pred nid -> Prop.
Variable ii : InductiveInv pr I.
Variables (A : Type) (this: nid).
Notation V := (mkWorld pr).
Notation W := (mkWorld (ProtocolWithIndInv ii)).
Variable (e : DT this V A).
Notation s := (spec_of e).
Section Prog.
Variable T : prog V A this.
Definition with_inv_set t := t = Unfinished \/ exists t', t' \In T /\ t = WithInv pr I ii (erefl _) t'.
Definition with_inv_prog := @Prog _ _ _ with_inv_set (or_introl (erefl _)).
End Prog.
Notation getS i := (getStatelet i l).
Definition with_inv_s : spec A := (fun i => s.1 i, fun i y m => m \In Coh W /\ s.2 i y m).
Definition with_inv := with_spec (DTbin_make with_inv_has_spec).
End InductiveInv.
Definition conseq (W : world) A this (e : DT this W A) (s : spec A) := forall i, s.1 i -> verify i e (s.2 i).
Hint Resolve conseq_refl : core.
Section Do.
Variable this : nid.
Variables (W : world) (A : Type) (s2 : spec A).
Variables (e : DT this W A) (pf : conseq e s2).
Definition do_prog := DTbin.prog_of (code_of e).
Definition do' := DTbin_make do_has_spec.
End Do.
Notation iinject x := (@inject _ _ _ _ _ _ x).
Notation uinject x := (@inject _ _ _ Unit _ _ x).
Notation "'Do' e" := (@do' _ _ _ _ e _) (at level 80).
Notation "x '<--' c1 ';' c2" := (bind c1 (fun x => c2)) (at level 81, right associativity).
Notation "c1 ';;' c2" := (bind c1 (fun _ => c2)) (at level 81, right associativity).

Lemma bot_spec : bot_prg \In has_spec this W s.
Proof.
by move=>i H C t ->; apply: alw_unfin.
