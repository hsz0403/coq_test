From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem.
From DiSeL Require Import Actions Injection InductiveInv.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section ProcessSyntax.
Variable this : nid.
Inductive proc (W : world) A := Unfinished | Ret of A | Act of action W A this | Seq B of proc W B & B -> proc W A | Inject V K of injects V W K & proc V A | WithInv p I (ii : InductiveInv p I) of W = mkWorld (ProtocolWithIndInv ii) & proc (mkWorld p) A.
Definition pcat W A B (t : proc W A) (k : A -> Pred (proc W B)) := [Pred s | exists q, s = Seq t q /\ forall x, q x \In k x].
Inductive schedule := ActStep | SeqRet | SeqStep of schedule | InjectStep of schedule | InjectRet | WithInvStep of schedule | WithInvRet.
End ProcessSyntax.
Arguments Unfinished {this W A}.
Arguments Ret [this W A].
Arguments Act [this W A].
Arguments Seq [this W A B].
Arguments WithInv [this W A].
Section ProcessSemantics.
Variable this : nid.
Fixpoint step (W : world) A (s1 : state) (p1 : proc this W A) sc (s2 : state) (p2 : proc this W A) : Prop := match sc, p1 with (* Action - make a step *) | ActStep, Act a => exists v pf, @a_step _ _ _ a s1 pf s2 v /\ p2 = Ret v (* Sequencing - apply a continuation *) | SeqRet, Seq _ (Ret v) k => s2 = s1 /\ p2 = k v | SeqStep sc', Seq _ p' k1 => exists p'', step s1 p' sc' s2 p'' /\ p2 = Seq p'' k1 (* Injection of a non-reduced term *) | InjectRet, Inject V K pf (Ret v) => exists s1', [/\ s2 = s1, p2 = Ret v & extends pf s1 s1'] | InjectStep sc', Inject V K pf t1' => exists s1' s2' s t2', [/\ p2 = Inject pf t2', s1 = s1' \+ s, s2 = s2' \+ s, s1' \In Coh V & step s1' t1' sc' s2' t2'] (* Imposing an inductive invariant on a non-reduced term *) | WithInvRet, WithInv p inv ii pf (Ret v) => exists s1', [/\ s2 = s1, p2 = Ret v & s1 = s1'] | WithInvStep sc', WithInv p inv ii pf t1' => exists t2', p2 = WithInv p inv ii pf t2' /\ step s1 t1' sc' s2 t2' | _, _ => False end.
Fixpoint good (W : world) A (p : proc this W A) sc : Prop := match sc, p with | ActStep, Act _ => True | SeqRet, Seq _ (Ret _) _ => True | SeqStep sc', Seq _ p' _ => good p' sc' | InjectStep sc', Inject _ _ _ p' => good p' sc' | InjectRet, Inject _ _ _ (Ret _) => True | WithInvStep sc', WithInv _ _ _ _ p' => good p' sc' | WithInvRet, WithInv _ _ _ _ (Ret _) => True | _, _ => False end.
Fixpoint safe (W : world) A (p : proc this W A) sc (s : state) : Prop := match sc, p with | ActStep, Act a => a_safe a s | SeqRet, Seq _ (Ret _) _ => True | SeqStep sc', Seq _ p' _ => safe p' sc' s | InjectStep sc', Inject V K pf p' => exists s', extends pf s s' /\ safe p' sc' s' | InjectRet, Inject V K pf (Ret _) => exists s', extends pf s s' | WithInvStep sc', WithInv _ _ _ _ p' => safe p' sc' s | WithInvRet, WithInv _ _ _ _ (Ret _) => True | _, _ => True end.
Definition pstep (W : world) A s1 (p1 : proc this W A) sc s2 p2 := [/\ s1 \In Coh W, safe p1 sc s1 & step s1 p1 sc s2 p2].
End ProcessSemantics.

Lemma proc_progress W A s (p : proc this W A) sc : s \In Coh W -> safe p sc s -> good p sc -> exists s' (p' : proc this W A), pstep s p sc s' p'.
Proof.
move=>C H1 H2; elim: sc W A s p H2 H1 C=>[||sc IH|sc IH||sc IH|]W A s.
-
case=>//=a _/= H; move/a_step_total: (H)=>[s'][r]H'.
by exists s', (Ret r); split=>//=; exists r, H.
-
by case=>//; move=>B p k/=; case: p=>//b _ _; exists s, (k b).
-
case=>//B p k/=H1 H2 C.
case: (IH W B s p H1 H2 C)=>s'[p'][G1 G2].
by exists s', (Seq p' k); split=>//; exists p'.
-
case=>// V K pf p/=H1 [z][E]H2 C.
case: (E)=>s3[Z] C1 C2.
case: (IH V A z p H1 H2 C1) =>s'[p']H3; case: H3=>S St.
exists (s' \+ s3), (Inject pf p'); split=>//; first by exists z.
by subst s; exists z, s', s3, p'.
-
case=>//V K pf; case=>// v/=_[s'] E C.
by exists s, (Ret v); split=>//=; exists s'.
-
case=>//pr I ii E p/= H1 H2 C.
have C' : s \In Coh (mkWorld pr) by subst W; apply: (with_inv_coh C).
case: (IH (mkWorld pr) A s p H1 H2 C')=>s'[p']H3.
exists s', (WithInv pr I ii E p'); split=>//=.
by exists p'; split=>//; case: H3.
-
case=>//pr I ii E; case=>//v/=_ _ C.
by exists s, (Ret v); split=>//=; exists s.
