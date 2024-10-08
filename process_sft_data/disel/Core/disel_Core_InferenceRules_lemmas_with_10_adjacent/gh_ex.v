From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Domain Freshness State EqTypeX DepMaps Protocols Worlds NetworkSem Rely.
From DiSeL Require Import Actions Injection Process Always HoareTriples InductiveInv.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Definition logvar {B A} (s : A -> spec B) : spec B := (fun i => exists x : A, (s x).1 i, fun y i m => forall x : A, (s x).2 y i m).
Definition binarify {A} (p : pre) (q : cont A) : spec A := (p, fun i y m => p i -> q y m).
Notation "'DHT' [ this , W ] ( p , q ) " := (DTbin this W (binarify p q)) (at level 0, format "'[hv ' DHT [ this , W ] ( '[' p , '/' q ']' ) ']'").
Notation "{ x .. y }, 'DHT' [ this , W ] ( p , q )" := (DTbin this W (logvar (fun x => .. (logvar (fun y => binarify p q)) .. ))) (at level 0, x binder, y binder, right associativity, format "'[hv ' { x .. y }, '/ ' DHT [ this , W ] ( '[' p , '/' q ']' ) ']'").
Section BasicRules.
Variable this : nid.
Arguments bind_rule [W A B e1 e2 i].
Section GhostRules.
Variables (W : world) (A B C : Type).
Variable (e : DT this W A).
Variables (s : C -> spec A) (f : DTbin this W (logvar s)).
End GhostRules.
Arguments gh_ex [W A C s f].
End BasicRules.
Section InjectLemmas.
Variable this : nid.
Variables (W V : world) (K : hooks) (A : Type) (w : injects V W K).
Notation W2 := (inj_ext w).
Variable (e1 : DT this V A).
End InjectLemmas.
Section InductiveInvLemmas.
Variable pr : protocol.
Notation l := (plab pr).
Variable I : dstatelet -> pred nid -> Prop.
Variable ii : InductiveInv pr I.
Variables (A : Type) (this: nid).
Notation V := (mkWorld pr).
Notation W := (mkWorld (ProtocolWithIndInv ii)).
Variable (e : DT this V A).
Notation getS i := (getStatelet i l).
End InductiveInvLemmas.

Lemma vrf_pre W A (e : DT this W A) i i' (k : cont A) : verify i e k -> network_rely W this i i' -> verify i' e k.
Proof.
move=>H M Ci' t H'; case: (rely_coh M)=>Ci _.
Admitted.

Lemma vrf_post W A (e : DT this W A) i (k : cont A) : verify i e k -> verify i e (fun x m => forall m', network_rely W this m m' -> k x m').
Proof.
move=>H Ci t H'; move: (alw_envsq (H Ci t H')).
Admitted.

Lemma bind_rule W A B (e1 : DT this W A) (e2 : A -> DT this W B) i (q : cont A) (r : cont B) : verify i e1 q -> (forall y j, q y j -> j \In Coh W -> verify j (e2 y) r) -> verify i (bind e1 e2) r.
Proof.
move=>H1 H2 Ci t [->|[t'][H3 H4]].
-
by apply: alw_unfin=>//; move/alw_coh: (H1 Unfinished (prog_unfin e1)).
Admitted.

Lemma step W A B (e1 : DT this W A) (e2 : A -> DT this W B) i (r : cont B) : verify i e1 (fun y m => verify m (e2 y) r) -> verify i (bind e1 e2) r.
Proof.
Admitted.

Lemma call_rule' W A i (f : DT this W A) (k : cont A) : (* Verify precondition of the call *) (i \In Coh W -> pre_of f i) -> (* Verify the rest out of the postcondition *) (forall x m, post_of f i x m -> m \In Coh W -> k x m) -> verify i f k.
Proof.
case: f=>s [e] /= H H1 H2 Ci t H3.
apply: aft_imp (H i t (H1 Ci) Ci H3).
Admitted.

Lemma call_rule W A (p : Pred state) (q : A -> Pred state) i {e} (k : cont A) : (i \In Coh W -> p i) -> (forall x m, q x m -> m \In Coh W -> k x m) -> verify i (@with_spec this W A (binarify p q) e) k.
Proof.
move=>H1 H2; apply: vrf_coh=>C; apply: call_rule'=>//.
Admitted.

Lemma vrf_mono (e : DT this W A) i (r1 r2 : cont A) : r1 <== r2 -> verify i e r1 -> verify i e r2.
Proof.
Admitted.

Lemma ghE (s : B -> C -> spec A) : conseq e (logvar (fun x => logvar (s x))) <-> conseq e (logvar (fun xy => s xy.1 xy.2)).
Proof.
split.
-
move=>/= H1 i [[x y]] H2.
have: exists x1 y1, (s x1 y1).1 i by exists x, y.
by move/H1; apply: vrf_mono=>y1 m1 T1 [x2 y2]; apply: (T1 x2 y2).
move=>/= H1 i [x][y] H2.
have: exists x, (s x.1 x.2).1 i by exists (x, y).
Admitted.

Lemma ghC (p : B -> pre) (q : B -> A -> pre) : (forall i x, p x i -> i \In Coh W -> verify i e (q x)) -> conseq e (logvar (fun x => binarify (p x) (q x))).
Proof.
move=>H i /= [x Hp] Ci t Ht.
have S : alwsafe i t by apply: alw_imp (H i x Hp Ci Ci t Ht).
Admitted.

Lemma gh_conseq t : conseq f (s t).
Proof.
case E: (s t)=>[a b] h /= H; apply: call_rule'=>[|x m].
-
by exists t; rewrite E.
Admitted.

Lemma act_rule W A (a: action W A this) i (r : cont A) : (forall j, network_rely W this i j -> a_safe a j /\ forall y k m, (exists pf : a_safe a j, a_step pf k y) -> network_rely W this k m -> r y m) -> verify i (act a) r.
Proof.
move=>H C p; case=>Z; subst p; first by apply: (alw_unfin C).
apply: (alw_act C)=>j R; case: (H j R)=>{H}S H; exists S.
split=>//k v m St R' v'[]<-.
have X: (exists pf : a_safe a j, a_step pf k v) by exists S.
Admitted.

Lemma ret_rule W A i (v : A) (r : cont A) : (forall m, network_rely W this i m -> r v m) -> verify i (ret this W v) r.
Proof.
move=>H C p; case=>Z; subst p; first by apply: alw_unfin.
Admitted.

Lemma inject_rule i j (r : cont A) : i \In Coh V -> verify i e1 (fun x i' => forall j', i' \+ j' \In Coh W -> network_rely W2 this j j' -> r x (i' \+ j')) -> verify (i \+ j) (inject w e1) r.
Proof.
move=>Ci H C t [->|[t' [H' ->{t}]]]; first by apply: alw_unfin.
move/aft_inject: {H H'} (H Ci _ H'); move/(_ _ _ w _ C).
apply: aft_imp=>v s Cs [i'][j'][E] Ci' S'.
Admitted.

Lemma with_inv_rule' i (r : cont A) : verify i e (fun x m => I (getS m) (nodes pr (getS m)) -> r x m) -> verify i (with_inv ii e) r.
Proof.
move=> H C t [->|[t' [H' ->{t}]]]; first by apply: alw_unfin.
move/aft_ind_inv: {H H'}(H (with_inv_coh C) _ H')=>/(_ _ _ C).
apply: aft_imp=>v m _[C']; apply.
Admitted.

Lemma with_inv_rule i (r : cont A) : verify i e (fun x m => r x m) -> verify i (with_inv ii e) r.
Proof.
move=>H; apply: with_inv_rule'.
Admitted.

Lemma gh_ex g i (k : cont A) : verify i (do' (@gh_conseq g)) k -> verify i (@with_spec this W A (logvar s) f) k.
Proof.
by [].
