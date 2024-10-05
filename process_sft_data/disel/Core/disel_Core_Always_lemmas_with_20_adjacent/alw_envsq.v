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

Lemma alw_refl A s (p : proc A) P : always s p P -> P s p.
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

Lemma alw_imp' A s (p : proc A) scs (P1 P2 : state -> proc A -> Prop) : (forall s p, s \In coherent -> P1 s p -> P2 s p) -> always_sc s p scs P1 -> always_sc s p scs P2.
Proof.
elim: scs s p=>[|sc scs IH] s p /= I; case=>C L; split=>// s2 E.
-
by apply: I (L _ E); case/rely_coh: E.
case/L: (E)=>S H T; split=>//; first by apply: I H; case/rely_coh: E.
Admitted.

Lemma alw_imp A s (p : proc A) (P1 P2 : state -> proc A -> Prop) : (forall s p, s \In coherent -> P1 s p -> P2 s p) -> always s p P1 -> always s p P2.
Proof.
Admitted.

Lemma alwA' A B s (p : proc A) scs (P : B -> state -> proc A -> Prop) : alwsafe_sc s p scs -> (always_sc s p scs (fun s' p' => forall x, P x s' p') <-> forall x, always_sc s p scs (fun s' p' => P x s' p')).
Proof.
move=>Ls; split=>[{Ls}|].
-
elim: scs s p=>[|sc scs IH] s p /= [C Et x]; split=>// s2; move/Et=>//.
by case=>S Ha L; split=>// s3 q; move/L/IH.
elim: scs s p Ls=>[|sc scs IH] s p /= [C Et Ha]; split=>// s2 E.
-
by move=>x; case: (Ha x)=>_; apply.
case/Et: (E)=>/= S _ L; split=>//.
-
by move=>x; case: (Ha x)=>_; case/(_ _ E).
move=>s3 q T; apply: IH; first by apply: L T.
Admitted.

Lemma alwA A B s (p : proc A) (P : B -> state -> proc A -> Prop) : alwsafe s p -> (always s p (fun s' p' => forall x, P x s' p') <-> forall x, always s p (fun s' p' => P x s' p')).
Proof.
move=>Ls; split.
-
by move=>H x ps; move: x; apply/(alwA' _ (Ls ps)).
Admitted.

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
Admitted.

Lemma alwI A s (p : proc A) (P : Prop) (Q : state -> proc A -> Prop) : alwsafe s p -> always s p (fun s' p' => P -> Q s' p') <-> (P -> always s p (fun s' p' => Q s' p')).
Proof.
move=>Ls; split; first by move=>H Hp scs; apply/alwI': Hp.
Admitted.

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
Admitted.

Lemma alwsafe_bnd A B (p1 : proc A) (p12 : proc B) s1 pp2 : p12 \In pcat p1 pp2 -> always s1 p1 (fun s2 p2 => forall p v, p2 = Ret v -> p \In pp2 v -> alwsafe s2 p) -> alwsafe s1 p12.
Proof.
move=>T Ls.
suff H: always s1 p12 (fun s p => forall v, p = Ret v -> True).
-
by apply: alw_imp H.
apply: alw_bnd T _; apply: alw_imp Ls=>s p _ I q v H.
Admitted.

Lemma aft_bnd A B (p1 : proc A) (p12 : proc B) pp2 s1 P : p12 \In pcat p1 pp2 -> after s1 p1 (fun v s => forall p, p \In pp2 v -> after s p P) -> after s1 p12 P.
Proof.
move=>T H; apply: alw_bnd T _.
Admitted.

Lemma aftI A s (p : proc A) (P : Prop) (Q : A -> state -> Prop) : alwsafe s p -> after s p (fun v s' => P -> Q v s') <-> (P -> after s p (fun v s' => Q v s')).
Proof.
move=>Ls; rewrite -(alwI Ls).
split; apply: alw_imp=>t q _ I.
-
by move=>Hp v; move/I; apply.
Admitted.

Lemma aft_alwsf A s (p : proc A) : alwsafe s p <-> after s p (fun v s => True).
Proof.
Admitted.

Lemma aft_imp A s (p : proc A) (P1 P2 : A -> state -> Prop) : (forall v s, s \In coherent -> P1 v s -> P2 v s) -> after s p P1 -> after s p P2.
Proof.
Admitted.

Lemma aftA A B s (p : proc A) (P : B -> A -> state -> Prop) : alwsafe s p -> (after s p (fun v s' => forall x, P x v s') <-> forall x, after s p (fun v s' => P x v s')).
Proof.
move=>Ls; rewrite -(alwA Ls).
split; apply: alw_imp=>t q _ I.
-
by move=>x v; move/I.
Admitted.

Lemma rely_ext i j s : i \In Coh V -> network_rely W this (i \+ j) s -> exists i' j', s = i' \+ j' /\ i' \In Coh V.
Proof.
move=>C M; case: (rely_coh M)=>_; rewrite (cohE w).
Admitted.

Lemma rely_split' z s1 s1' s2 s2' : s1 \In Coh V -> s2 \In Coh V -> network_step W z (s1 \+ s1') (s2 \+ s2') -> network_step V z s1 s2 /\ network_step (inj_ext w) z s1' s2'.
Proof.
move=>C1 C2 N.
case: (sem_split w C1 C2 N); case=>R E; [subst s2'|subst s2]; split=>//; apply: Idle; split=>//.
case: (step_coh N)=>C _.
case/(cohE w): (C)=>s3[s4][E]C' C''.
move: (coh_prec (cohS C) C1 C' E)=>Z; subst s3.
Admitted.

Lemma alw_envsq A s1 (p1 : proc A) (P : _ -> _ -> Prop) : always s1 p1 P -> always s1 p1 (fun s2 p2 => forall s3, network_rely W this s2 s3 -> P s3 p2).
Proof.
by move=>H scs; apply: alwp_envsq (H scs).
