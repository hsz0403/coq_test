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

Lemma with_inv_rule' i (r : cont A) : verify i e (fun x m => I (getS m) (nodes pr (getS m)) -> r x m) -> verify i (with_inv ii e) r.
Proof.
move=> H C t [->|[t' [H' ->{t}]]]; first by apply: alw_unfin.
move/aft_ind_inv: {H H'}(H (with_inv_coh C) _ H')=>/(_ _ _ C).
apply: aft_imp=>v m _[C']; apply.
by case: C'=>_ _ _ _/(_ l); rewrite prEq; case.
