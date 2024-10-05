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

Lemma alwI' A s (p : proc A) scs (P : Prop) (Q : state -> proc A -> Prop) : alwsafe s p -> (always_sc s p scs (fun s' p' => P -> Q s' p') <-> (P -> always_sc s p scs (fun s' p' => Q s' p'))).
Proof.
move=>Ls; split.
-
elim: scs s p Ls=>[|sc scs IH] s p Ls /= [C Et H]; split=>// s2.
-
by move/Et; apply.
move=>M; move: (alw_envs Ls M)=>{Ls} Ls.
case/Et: M=>H1 /(_ H) H2 H3; split=>// s3 q T.
by apply: IH H; [apply: alw_step T | apply: H3].
elim: scs s p Ls=>[|sc scs IH] s p /= Ls H; move: (alw_coh Ls)=>C; split=>// s2 M; first by case/H=>_; apply.
move: (alw_envs Ls M)=>{Ls} Ls.
split; first by move/alw_safe: Ls.
-
by case/H=>_; case/(_ _ M).
move=>s3 q T; move: (alw_step Ls T)=>{Ls} Ls.
by apply: IH Ls _; case/H=>_; case/(_ _ M)=>_ _; apply.
