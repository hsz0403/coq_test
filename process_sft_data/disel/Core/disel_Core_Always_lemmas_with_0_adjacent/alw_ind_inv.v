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

Lemma alw_ind_inv (p : proc this V A) (P : state -> proc this V A -> Prop) i : i \In Coh W -> always i p P -> always i (WithInv pr I ii (erefl _) p) (fun m q => m \In Coh W /\ ((exists q', q = WithInv pr I ii (erefl _) q' /\ P m q') \/ (exists v', q = Ret v' /\ P m (Ret v')))).
Proof.
move=>C Ls scs; elim: scs i p C Ls=>[|sc scs IH] i p C Ls /=; split=>//{C}s M; move: (alw_coh Ls) (proj2 (rely_coh M))=>Ci C.
-
split; first by case:(rely_coh M)=>_/with_inv_coh.
left; exists p; split=>//; apply: alw_refl.
by move/with_inv_rely': M; apply: (alw_envs).
split.
-
case: sc=>//; last by case: p Ls=>//.
move=>sc; move: (alw_safe Ls sc)=>Sf.
by move/with_inv_rely': M; move/(alw_envs Ls)=>H; apply: (alw_safe H).
-
split=>//; left; exists p; split=>//.
by move/with_inv_rely': M; move/(alw_envs Ls)=>H; apply: alw_refl.
move=>s' q/stepWithInv=>H; case: H Ls.
-
case=>[v][Z1]Z2 Z3 Z4 _ _ Ls; subst s' p q sc.
apply: alw_ret'=>//=s' M'.
split; first by case/rely_coh: M'.
right; exists v; split=>//.
by move: (rely_trans M M')=>/with_inv_rely'/(alw_envs Ls)/alw_refl.
case=>sc'[q'][Z1]Z2 _ _ T Ls; subst q sc.
have X: s' \In Coh W by apply: (pstep_inv (proj2 (rely_coh M)) T).
move/with_inv_rely': (M)=>/(alw_envs Ls)=>Ls'.
move/(alw_step Ls'): T=>{Ls'} Ls'.
by apply: IH.
