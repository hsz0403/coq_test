From Undecidability.L Require Import Computability.Decidability Datatypes.LNat L.
Require Import Nat.
Fixpoint boundb (k : nat) (t : term) : bool := match t with | var n => negb (k <=? n) | app s t => andb (boundb k s) (boundb k t) | lam s => boundb (S k) s end.
Instance term_boundb : computableTime' boundb (fun _ _ => (5,fun s _ => (size s * 31+9,tt))).
Proof.
extract.
solverec.
unfold c__leb2, leb_time, c__leb.
nia.
Definition closedb := boundb 0.
Instance termT_closedb : computableTime' closedb (fun s _ => (size s * 31+15,tt)).
Proof.
change closedb with (fun x => boundb 0 x).
extract.
solverec.
Definition lambdab (t : term) : bool := match t with | lam _ => true | _ => false end.
Instance term_lambdab : computableTime' lambdab (fun _ _ => (11,tt)).
Proof.
extract.
solverec.

Instance term_boundb : computableTime' boundb (fun _ _ => (5,fun s _ => (size s * 31+9,tt))).
Proof.
extract.
solverec.
unfold c__leb2, leb_time, c__leb.
Admitted.

Lemma boundb_spec k t : Bool.reflect (bound k t) (boundb k t).
Proof.
revert k.
induction t;intros;cbn.
simpl.
-
destruct (Nat.leb_spec0 k n); simpl;constructor.
intros H.
inv H.
lia.
constructor.
lia.
-
specialize (IHt1 k).
specialize (IHt2 k).
inv IHt1;simpl.
+
inv IHt2;constructor.
*
now constructor.
*
intros C.
now inv C.
+
constructor.
intros C.
now inv C.
-
specialize (IHt (S k)).
inv IHt;constructor.
+
now constructor.
+
intros C.
Admitted.

Lemma closedb_spec s : Bool.reflect (closed s) (closedb s).
Proof.
unfold closedb.
Admitted.

Instance term_lambdab : computableTime' lambdab (fun _ _ => (11,tt)).
Proof.
extract.
Admitted.

Lemma lambdab_spec t : Bool.reflect (lambda t) (lambdab t).
Proof.
Admitted.

Lemma ldec_lambda : ldec lambda.
Proof.
apply (dec_ldec lambdab).
Admitted.

Lemma ldec_closed : ldec closed.
Proof.
apply (dec_ldec closedb).
Admitted.

Lemma ldec_proc : ldec proc.
Proof.
apply ldec_conj.
apply ldec_closed.
Admitted.

Instance termT_closedb : computableTime' closedb (fun s _ => (size s * 31+15,tt)).
Proof.
change closedb with (fun x => boundb 0 x).
extract.
solverec.
