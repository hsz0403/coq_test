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

Lemma alw_bnd A B (p1 : proc A) (p12 : proc B) pp2 s1 (P : state -> B -> Prop) : p12 \In pcat p1 pp2 -> always s1 p1 (fun s2 p2 => (* p2 is a process resulting from executing p1 *) forall p v, p2 = Ret v -> p \In pp2 v -> (* Now assume p2 is a return and p is its continuation, so we proceed until we reach the return *) always s2 p (fun s q => forall v, q = Ret v -> P s v)) -> always s1 p12 (fun s p => forall v, p = Ret v -> P s v).
Proof.
move=>Tc Ls scs.
elim: scs s1 p1 p12 Tc Ls=>[|sc scs IH] s1 p1 p12 Tc Ls /=.
-
by split=>[|s2]; [apply: alw_coh Ls | case: Tc=>k [->]].
split=>[|s2 E]; first by apply: alw_coh Ls.
case: Tc IH=>k [->{p12}] H IH.
split=>//; last first.
-
move=>s3 q T; case/stepSeq: T Ls.
-
case=>v [_ ->->-> C]; move/alw_refl/(_ _ _ (erefl _)).
by move/(_ _ (H v))/alw_envs; apply.
case=>sc' [p'][_ ->{q}] T; move/alw_envs/(_ E)/alw_step.
by move/(_ _ _ _ T)/IH; apply; exists k.
move/(alw_envs Ls): E=>{Ls} Ls.
have Ls': always s2 p1 (fun s2 p2 => forall sc p v, p2 = Ret v -> p \In pp2 v -> safe p sc s2).
-
by apply: alw_imp Ls=>s p _ I sc' q v E; move/(I _ _ E)/alw_safe.
case: sc=>//=; first by case: p1 {Ls} Ls'.
move=>sc; case: (Ls [:: sc])=>C.
by move/(_ _ (rely_refl this C)); case.
