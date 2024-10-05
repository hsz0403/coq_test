From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness DepMaps EqTypeX.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section TaggedMessages.
Structure TaggedMessage := TMsg { tag: nat; (* Okay, this is a big omissin, but for now I'm sick and tired to deal with casts everywhere, so for the moment the contents of the messages are going to be just sequences of natural number, and it's up to the client-supplied coherence predicate to restrict them appropriately, relating this thing to tags *) tms_cont :> seq nat }.
End TaggedMessages.
Section Shared.
Definition Label := [ordType of nat].
Structure msg (mtype : Type) := Msg {content : mtype; from : nat; to : nat; active : bool }.
Definition mid := [ordType of nat].
Definition soup : Type := union_map mid (msg (TaggedMessage)).
Variables (s: soup) (V: valid s).
Definition post_msg m : soup * mid := let: f := fresh s in (s \+ f \\-> m, f).
Definition mark_msg T (m : msg T) : msg T := Msg (content m) (from m) (to m) false.
Definition consume_msg (s : soup) (id : mid) : soup := let: mr := find id s in if mr is Some m then upd id (mark_msg m) s else s.
Definition is_active (id : mid) := exists m, find id s = Some m /\ active m.
Definition is_consumed (id : mid) := exists m, find id s = Some m /\ ~~ active m.
Notation "'{{' m 'in' s 'at' id '}}'" := (find id s = Some m).
Notation "'{{' m 'in' s '}}'" := (exists id, {{m in s at id}}).
End Shared.
Section Local.
Variable U : Type.
Definition nid := nat.
Definition lstate_type := union_map [ordType of nid] U.
End Local.
Section Statelets.
Structure dstatelet := DStatelet { (* Not sure if it's the best way to represent information about kinds of messages in this particular dstatelet, but let's think of tags as of integers for now, so dTagToCont will map the tags to specific types. *) (* Local state for each node as a pair of heaps; first heap is real, second heap is a ghost one. Let's deal with this model for now before we figure out how to discharge equalities in a better way *) dstate : lstate_type heap; dsoup : soup }.
Fixpoint empty_lstate (ns : seq nid) := if ns is n :: ns' then n \\-> Heap.empty \+ (empty_lstate ns') else Unit.
Definition empty_dstatelet : dstatelet := @DStatelet (empty_lstate [::]) Unit.
End Statelets.
Module StateGetters.
Section StateGetters.
Definition state := union_map Label dstatelet.
Definition getStatelet (s: state) (i : Label) : dstatelet := match find i s with | Some d => d | None => empty_dstatelet end.
End StateGetters.
End StateGetters.
Export StateGetters.

Lemma post_valid m : valid (post_msg m).1.
Proof.
Admitted.

Lemma post_fresh m : (post_msg m).2 \notin dom s.
Proof.
Admitted.

Lemma find_consume s' (id: mid) m: valid s' -> find id s' = Some m -> find id (consume_msg s' id) = Some (mark_msg m).
Proof.
Admitted.

Lemma find_mark m s' msg : valid s' -> find m (consume_msg s' m) = Some msg -> exists msg', find m s' = Some msg' /\ msg = mark_msg msg'.
Proof.
move=>V'; rewrite /consume_msg; case D: (m \in dom s').
-
move/um_eta: D=>[msg'][->]_; rewrite findU eqxx/= V'.
by case=><-; eexists _.
Admitted.

Lemma mark_other m m' s' : valid s' -> m' == m = false -> find m' (consume_msg s' m) = find m' s'.
Proof.
move=>V' N; rewrite /consume_msg; case D: (m \in dom s').
by case: dom_find (D)=>//v->_ _; rewrite findU N.
Admitted.

Lemma consume_valid s' m : valid s' -> valid (consume_msg s' m).
Proof.
move=>V'; rewrite /consume_msg; case (find m s')=>//v.
Admitted.

Lemma consumeUn (s': soup) (i : mid) mm (j : mid) : valid (s' \+ i \\-> mm) -> consume_msg (s' \+ i \\-> mm) j = if i == j then s' \+ i \\-> mark_msg mm else (consume_msg s' j) \+ (i \\-> mm).
Proof.
rewrite ![_ \+ i \\-> _]joinC; rewrite eq_sym.
move=>V'; case B: (j==i); rewrite /consume_msg findPtUn2// B.
-
by move/eqP: B=>?; subst j; rewrite updPtUn.
Admitted.

Lemma valid_mt_state : valid (dstate empty_dstatelet).
Proof.
Admitted.

Lemma mt_nodes : dom (dstate empty_dstatelet) =i [::].
Proof.
Admitted.

Lemma valid_mt_soup : valid (dsoup empty_dstatelet).
Proof.
by rewrite /= valid_unit.
