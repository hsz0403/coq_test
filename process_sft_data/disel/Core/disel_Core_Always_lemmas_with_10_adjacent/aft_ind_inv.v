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
Admitted.

Lemma alw_inject (p : proc this V A) (P : state -> proc this V A -> Prop) i j : i \+ j \In Coh W -> always i p P -> always (i \+ j) (Inject w p) (fun m q => exists i' j', [/\ m = i' \+ j', i' \In Coh V, network_rely W2 this j j' & (exists q', q = Inject w q' /\ P i' q') \/ (exists v', q = Ret v' /\ P i' (Ret v'))]).
Proof.
move=>C Ls scs; elim: scs i j p C Ls=>[|sc scs IH] i j p C Ls /=; split=>// {C} s M; move: (alw_coh Ls) (proj2 (rely_coh M))=>Ci C; case/(rely_ext Ci): M C (M)=>i1 [j1][->{s}] Ci1 C; case/(rely_split Ci Ci1)=> /(alw_envs Ls) {Ls} Ls S1.
-
by exists i1, j1; split=>//; left; exists p; move/alw_refl: Ls.
split.
-
case: sc=>//; last by case: p Ls=>// v; exists i1, j1.
by move=>sc; move: (alw_safe Ls sc)=>Sf; exists i1; split=>//; exists j1.
-
by exists i1, j1; split=>//; left; exists p; move/alw_refl: Ls.
move=>s q; rewrite stepInject => H.
case: H Ls.
-
case=>_ [v][_ ->->->{p q s} _] Ls; apply: alw_ret'=>// s M.
case/(rely_ext Ci1): M (M)=>i2 [j2][->{s}] Ci2.
case/(rely_split Ci1 Ci2)=> /(alw_envs Ls) {Ls} Ls S2.
exists i2, j2; split=>//; first by apply: rely_trans S1 S2.
by right; exists v; move/alw_refl: Ls.
case=>sc' [q'][x1][i2][y1][_ -> E -> {sc q s}] _ T Ls.
have [E1 E2] : x1 = i1 /\ y1 = j1.
-
case: T=>Cx1 _.
move: (coh_prec (cohS C) Ci1 Cx1 E) (E)=><-{E Cx1 x1}.
by move/(joinxK (cohS C)).
rewrite {E x1}E1 {y1}E2 in T *.
have C' : i2 \+ j1 \In Coh W.
-
move: (C)=>C'; rewrite (cohE w) in C *=>[[s1]][s2][E]D1 D2.
move: (coh_prec (cohS C') Ci1 D1 E)=>Z; subst i1.
move: (joinxK (cohS C') E)=>Z; subst s2; clear E.
apply/(cohE w); exists i2, j1; split=>//.
by case/step_coh: (pstep_network_sem T).
move/(alw_step Ls): T=>{Ls} Ls.
apply: alw_imp' (IH _ _ _ C' Ls)=>{IH Ls C' C Ci Ci1 i i1 i2 p q' sc' scs}.
move=>s p _ [i2][j2][->{s}] Ci2 S2 H; exists i2, j2; split=>//.
Admitted.

Lemma aft_inject (p : proc this V A) (P : A -> state -> Prop) i j : i \+ j \In Coh W -> after i p P -> after (i \+ j) (Inject w p) (fun v m => exists i' j', [/\ m = i' \+ j', i' \In Coh V, network_rely W2 this j j' & P v i']).
Proof.
move=>C /(alw_inject C); apply: alw_imp=>{p i C} s q _.
case=>i1 [j1][->{s} Ci1 S1] H v E.
move: E H=>-> [[q'][//]|[_][[<-]] H].
Admitted.

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
Admitted.

Lemma aft_ind_inv (p : proc this V A) (P : A -> state -> Prop) i : i \In Coh W -> after i p P -> after i (WithInv pr I ii (erefl _) p) (fun v m => m \In Coh W /\ P v m).
Proof.
move=>C /(alw_ind_inv C); apply: alw_imp=>{p i C} s q _.
case=>C H; split=>//; subst q.
case:H; first by move=>[?]; case.
by case=>v'[][]<-{v'}/(_ v (erefl _)).
