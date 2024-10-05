From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL Require Import Actions Injection Process InductiveInv.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Always.
Variable this : nid.
Variable W : world.
Notation coherent := (Coh W).
Arguments proc [this W].
Fixpoint always_sc A (s1 : state) p scs (P : state -> proc A -> Prop) : Prop := s1 \In coherent /\ if scs is sc :: scs' then forall s2, network_rely W this s1 s2 -> [/\ safe p sc s2, P s2 p & forall s3 q, @pstep this W A s2 p sc s3 q -> always_sc s3 q scs' P] else forall s2, network_rely W this s1 s2 -> P s2 p.
Definition always A s (p : proc A) P := forall scs, always_sc s p scs P.
Notation alwsafe_sc s p scs := (always_sc s p scs (fun _ _ => True)).
Notation alwsafe s p := (always s p (fun _ _ => True)).
Arguments alwA [A B s p P].
Arguments alwI [A s p P Q].
Definition after A s (p : proc A) (P : A -> state -> Prop) := always s p (fun s2 p2 => forall v, p2 = Ret v -> P v s2).
Arguments aftA [A B s p P].
Arguments aftI [A s p P Q].
End Always.
Section AlwaysInject.
Variables (V W : world) (K : hooks) (A : Type) (w : injects V W K) (this: nid).
Notation W2 := (inj_ext w).
End AlwaysInject.
Notation alwsafe_sc s p scs := (always_sc s p scs (fun _ _ => True)).
Notation alwsafe s p := (always s p (fun _ _ => True)).
Module AlwaysInductiveInv.
Section AlwaysInductiveInv.
Import InductiveInv.
Variable pr : protocol.
Notation l := (plab pr).
Notation coh := (coh pr).
Variable I : dstatelet -> pred nid -> Prop.
Variable ii : InductiveInv pr I.
Variables (A : Type) (this: nid).
Notation V := (mkWorld pr).
Notation W := (mkWorld (ProtocolWithIndInv ii)).
End AlwaysInductiveInv.
End AlwaysInductiveInv.
Export AlwaysInductiveInv.

Lemma alw_coh' A s (p : proc A) scs P : always_sc s p scs P -> s \In coherent.
Proof.
Admitted.

Lemma alw_coh A s (p : proc A) P : always s p P -> s \In coherent.
Proof.
Admitted.

Lemma alw_safe' A s (p : proc A) sc scs P : always_sc s p (sc :: scs) P -> safe p sc s.
Proof.
Admitted.

Lemma alw_safe A s (p : proc A) P : always s p P -> forall sc, safe p sc s.
Proof.
Admitted.

Lemma alw_refl' A s (p : proc A) sc P : always_sc s p sc P -> P s p.
Proof.
Admitted.

Lemma alw_envs' A s1 (p : proc A) scs s2 P : always_sc s1 p scs P -> network_rely W this s1 s2 -> always_sc s2 p scs P.
Proof.
Admitted.

Lemma alw_envs A s1 (p : proc A) s2 P : always s1 p P -> network_rely W this s1 s2 -> always s2 p P.
Proof.
Admitted.

Lemma alw_step A s1 (p : proc A) sc s2 q P : always s1 p P -> pstep s1 p sc s2 q -> always s2 q P.
Proof.
move=>Ls Ts; move: (Ls [:: sc])=>/= [C].
case/(_ _ (rely_refl this C))=>_ _; move/(_ _ _ Ts)=>_.
move=>scs; move: (Ls (sc :: scs))=>/= [_].
Admitted.

Lemma alwp_envsq A s1 (p1 : proc A) scs (P : _ -> _ -> Prop) : always_sc s1 p1 scs P -> always_sc s1 p1 scs (fun s2 p2 => forall s3, network_rely W this s2 s3 -> P s3 p2).
Proof.
elim: scs s1 p1=>[|sc scs IH] /= s1 p1 [C H]; split=>// s2 M.
-
by move=>s3 /(rely_trans M); apply: H.
split; first by case: (H _ M).
-
by move=>s3 /(rely_trans M) /H; case.
Admitted.

Lemma alw_envsq A s1 (p1 : proc A) (P : _ -> _ -> Prop) : always s1 p1 P -> always s1 p1 (fun s2 p2 => forall s3, network_rely W this s2 s3 -> P s3 p2).
Proof.
Admitted.

Lemma alw_unfin' A s1 scs (P : state -> proc A -> Prop) : s1 \In coherent -> (forall s2, network_rely W this s1 s2 -> P s2 Unfinished) -> always_sc s1 Unfinished scs P.
Proof.
case: scs=>[|sc scs] C H; split=>// s2 E.
split=>[||s3 q/stepUnfin]//; first by case: sc=>//.
Admitted.

Lemma alw_unfin A s1 (P : state -> proc A -> Prop) : s1 \In coherent -> (forall s2, network_rely W this s1 s2 -> P s2 Unfinished) -> always s1 Unfinished P.
Proof.
Admitted.

Lemma alw_ret' A s1 (v : A) scs (P : state -> proc A -> Prop) : s1 \In coherent -> (forall s2, network_rely W this s1 s2 -> P s2 (Ret v)) -> always_sc s1 (Ret v) scs P.
Proof.
case: scs=>[|sc scs] C H; split=>// s2 E.
split; last by [move=>s3 q; move/stepRet].
-
by case: sc.
Admitted.

Lemma alw_ret A s1 (v : A) (P : state -> proc A -> Prop) : s1 \In coherent -> (forall s2, network_rely W this s1 s2 -> P s2 (Ret v)) -> always s1 (Ret v) P.
Proof.
Admitted.

Lemma alw_act A s1 (a : action W A this) (P : state -> proc A -> Prop) : s1 \In coherent -> (forall s2, network_rely W this s1 s2 -> exists S : a_safe a s2, P s2 (Act a) /\ forall s3 v s4, a_step S s3 v -> network_rely W this s3 s4 -> P s4 (Ret v)) -> always s1 (Act a) P.
Proof.
move=>C H [|sc scs]; split=>// s2; case/H=>// H1[H2]H3//.
split=>//; first by case: sc.
move=>s3 q /stepAct [v][pf][_ -> St].
rewrite (pf_irr H1 pf) in H3.
apply: alw_ret'; last by move=>s4; apply: H3 St.
Admitted.

Lemma alw_refl A s (p : proc A) P : always s p P -> P s p.
Proof.
by move/(_ [::])/alw_refl'.
