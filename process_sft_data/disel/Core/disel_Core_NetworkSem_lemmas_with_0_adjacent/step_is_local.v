From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section NetworkSemantics.
Variable w : world.
Variable this: nid.
Notation getl := (getLocal).
Notation gets := (getStatelet).
Notation getp := (@getProtocol w).
Definition get_coh l := @coh (getp l).
Definition get_st l := @snd_trans (getp l).
Definition get_rt l := @rcv_trans (getp l).
Definition all_hooks_fire (h : hooks) l st s n (msg : seq nat) to := (* For any hook associated with client protocol l and send-tag st *) forall z lc hk, Some hk = find ((z, lc), (l, st)) h -> lc \in dom s -> l \in dom s -> let: core_local := getl n (gets s lc) in let: client_local := getl n (gets s l) in hk core_local client_local msg to.
Inductive network_step (s1 s2 : state) : Prop := (* Do nothing *) Idle of s1 \In Coh w /\ s1 = s2 (* Send message *) | SendMsg (* Pick a world, send transition and a recipient *) l st (_ : st \In @get_st l) to msg b (pf: this \in (nodes (getp l) (gets s1 l))) (pf' : l \in dom s1) (C: Coh w s1) (* It's safe to send *) (S : send_safe st this to (gets s1 l) msg) (* All hooks are applicable *) (pf_hooks : all_hooks_fire (geth w) l (t_snd st) s1 this msg to) (* b is a result of executing the transition *) (spf : Some b = send_step S) of (* Generate the message and the new local state *) let: d := gets s1 l in (* Update the soup and local state *) let: f' := upd this b (dstate d) in let: s' := (post_msg (dsoup d) (Msg (TMsg (t_snd st) msg) this to true)).1 in s2 = upd l (DStatelet f' s') s1 | ReceiveMsg l rt (_ : rt \In @get_rt l) i from (* Pick a world, receive transition and a message *) (pf: this \in (nodes (getp l)) (gets s1 l)) (pf': l \in dom s1) (C: Coh w s1) (msg : TaggedMessage) (pf': tag msg = t_rcv rt) of let: d := (gets s1 l) in let: f := dstate d in let: s := dsoup d in [/\ find i s = Some (Msg msg from this true), msg_wf rt (coh_s l C) this from msg & (* The semantics doesn't execute unsafe receive-transitions *) let loc' := receive_step rt from msg (coh_s l C) pf in let: f' := upd this loc' f in let: s'' := consume_msg s i in s2 = upd l (DStatelet f' s'') s1].
End NetworkSemantics.

Lemma step_is_local s1 s2 l: network_step s1 s2 -> forall z, z != this -> find z (dstate (gets s1 l)) = find z (dstate (gets s2 l)).
Proof.
move=>S z N; case: S; first by case=>_ Z; subst s2.
-
move=>k st ? to a b pf D C S Ph Spf Z; subst s2; case B: (l == k); rewrite /gets findU B //= (cohS C)/=.
by move/negbTE: N; rewrite findU=>->/=; move/eqP: B=>->.
move=>k rt ? i from H1 H2 C msg T/= [H3 H4]Z; subst s2.
case B: (l == k); rewrite /gets findU B //= (cohS C)/=.
by move/negbTE: N; rewrite findU=>->/=; move/eqP: B=>->.
