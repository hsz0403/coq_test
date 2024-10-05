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
by apply: rely_trans S1 S2.
