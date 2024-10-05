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

Lemma rely_split s1 s1' s2 s2' : s1 \In Coh V -> s2 \In Coh V -> network_rely W this (s1 \+ s1') (s2 \+ s2') -> network_rely V this s1 s2 /\ network_rely (inj_ext w) this s1' s2'.
Proof.
move=>C1 C2 [n E].
elim: n s1 s1' E C1 C2=>[|n IH] /= s1 s1'; last first.
-
move=>[z][s3][N]H1 H2 C1 C2.
case: (step_coh H1)=>D1 D2; move/(cohE w): D2=>[s4][s5][Z]C3 C4.
subst s3; case: (IH s4 s5 H2 C3 C2)=>G1 G2.
case: (rely_split' C1 _ H1)=>//H3 H4; split=>//.
+
by case: G1=>m R; exists m.+1, z, s4.
by case: G2=>m R; exists m.+1, z, s5.
move=> [E1 E2] C1 C2.
move: (coh_prec (cohS E2) C1 C2 E1)=>Z; subst s2.
rewrite (joinxK (cohS E2) E1); split; exists 0=>//.
split=>//; rewrite -(joinxK (cohS E2) E1)=>{E1 s2' C2}.
move/(cohE w): (E2)=>[t1][t2][E]C' C''.
move: ((coh_prec (cohS E2)) C1 C' E)=>Z; subst t1.
by rewrite (joinxK (cohS E2) E).
