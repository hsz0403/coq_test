From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module WorldGetters.
Section WorldGetters.
Definition context := union_map Label protocol.
Definition hook_domain := [ordType of ((nat * Label) * (Label * nat))%type].
Definition hook_type := heap -> heap -> seq nat -> nid -> Prop.
Definition hooks := union_map hook_domain hook_type.
Definition world := (context * hooks)%type.
Definition getc (w: world) : context := fst w.
Coercion getc : world >-> context.
Definition geth (w: world) : hooks := snd w.
Coercion geth : world >-> hooks.
Variable w : world.
Variables (p : protocol).
Definition getProtocol i : protocol:= match find i (getc w) with | Some p => p | None => EmptyProt i end.
End WorldGetters.
End WorldGetters.
Export WorldGetters.
Module Worlds.
Module Core.
Section Core.
Definition hooks_consistent (c : context) (h : hooks) : Prop := forall z lc ls t, ((z, lc), (ls, t)) \in dom h -> (lc \in dom c) && (ls \in dom c).
Definition hook_complete w := hooks_consistent (getc w) (geth w).
Definition Coh (w : world) : Pred state := fun s => let: c := fst w in let: h := snd w in [/\ valid w, valid s, hook_complete w, dom c =i dom s & forall l, coh (getProtocol w l) (getStatelet s l)].
Section MakeWorld.
Variable p : protocol.
Notation l := (plab p).
Definition mkWorld : world := (l \\-> p, Unit).
End MakeWorld.
End Core.
End Core.
End Worlds.
Export Worlds.Core.

Lemma cohW w s : Coh w s -> valid w.
Proof.
by case w=>[c h]; case.
