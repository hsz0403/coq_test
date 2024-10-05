From Undecidability.L Require Export Tactics.LTactics Functions.Encoding Datatypes.LBool L.
Import HOAS_Notations.
Definition decides (u:term) P := forall (s:term), exists b : bool, (app u (ext s) == ext b /\ (if b then P s else ~P s)).
Definition ldec (P : term -> Prop) := exists u : term, proc u /\ decides u P.
Definition complement (P : term -> Prop) := fun t => ~ P t.
Definition conj (P : term -> Prop) (Q : term -> Prop) := fun t => P t /\ Q t.
Definition disj (P : term -> Prop) (Q : term -> Prop) := fun t => P t \/ Q t.
Definition tcompl (u : term) : term := Eval cbn in convert (λ x, !!(ext negb) (!!u x)).
Definition tconj (u v : term) : term := Eval cbn in convert (λ x, !!(ext andb) (!!u x) (!!v x)).
Definition tdisj (u v : term) : term := Eval cbn in convert (λ x, !!(ext orb) (!!u x) (!!v x)).
Hint Unfold tcompl tconj tdisj : Lrewrite.
Hint Opaque tcompl tconj tdisj : Lrewrite.
Hint Unfold tcompl tconj tdisj : LProc.
Hint Opaque tcompl tconj tdisj : LProc.
Arguments dec_ldec {_} f {_} _.

Lemma ldec_complement P : ldec P -> ldec (complement P).
Proof.
intros [u [[cls_u lam_u] H]].
exists (tcompl u).
unfold tcompl.
split.
Lproc.
intros s.
destruct (H s) as [b [A Ps]];exists (negb b).
split.
-
Lsimpl.
rewrite A.
now Lsimpl.
-
Admitted.

Lemma ldec_disj P Q : ldec P -> ldec Q -> ldec (disj P Q).
Proof.
intros [u [[cls_u lam_u] decP]] [v [[cls_v lam_v] decQ]].
exists (tdisj u v).
unfold tdisj.
split.
Lproc.
intros s.
destruct (decP s) as [b [Hu Ps]], (decQ s) as [b' [Hv Qs]];exists (orb b b').
split.
-
Lsimpl.
rewrite Hu,Hv.
now Lsimpl.
-
Admitted.

Lemma dec_ldec (P:term -> Prop) (f: term -> bool) {If : computable f}: (forall x, reflect (P x) (f x)) ->ldec P.
Proof.
intros H.
exists (ext f).
split.
Lproc.
intros s.
eexists.
split.
-
Lsimpl.
reflexivity.
-
Admitted.

Lemma ldec_conj P Q : ldec P -> ldec Q -> ldec (conj P Q).
Proof.
intros [u [[cls_u lam_u] decP]] [v [[cls_v lam_v] decQ]].
exists (tconj u v).
unfold tconj.
split.
Lproc.
intros s.
destruct (decP s) as [b [Hu Ps]], (decQ s) as [b' [Hv Qs]];exists (andb b b').
split.
-
Lsimpl.
rewrite Hu,Hv.
now Lsimpl.
-
destruct b,b';simpl;unfold conj;intuition.
