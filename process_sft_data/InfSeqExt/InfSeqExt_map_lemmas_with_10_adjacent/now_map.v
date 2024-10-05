Require Import InfSeqExt.infseq.
Require Import InfSeqExt.exteq.
Section sec_map.
Variable A B: Type.
CoFixpoint map (f: A->B) (s: infseq A): infseq B := match s with | Cons x s => Cons (f x) (map f s) end.
End sec_map.
Arguments map [A B] _ _.
Arguments map_Cons [A B] _ _ _.
Section sec_zip.
Variable A B: Type.
CoFixpoint zip (sA: infseq A) (sB: infseq B) : infseq (A*B) := match sA, sB with | Cons a sA0, Cons b sB0 => Cons (a, b) (zip sA0 sB0) end.
End sec_zip.
Arguments zip [A B] _ _.
Arguments zip_Cons [A B] _ _ _ _.
Section sec_map_modalop.
Variable A B: Type.
Definition fstAB := fst (A:=A) (B:=B).
End sec_map_modalop.
Arguments and_tl_map [A B f P P' Q Q'] _ _ [s] _.
Arguments and_tl_map_conv [A B f P P' Q Q'] _ _ [s] _.
Arguments or_tl_map [A B f P P' Q Q'] _ _ [s] _.
Arguments or_tl_map_conv [A B f P P' Q Q'] _ _ [s] _.
Arguments impl_tl_map [A B f P P' Q Q'] _ _ [s] _ _.
Arguments impl_tl_map_conv [A B f P P' Q Q'] _ _ [s] _ _.
Arguments not_tl_map [A B f P Q] _ [s] _ _.
Arguments not_tl_map_conv [A B f P Q] _ [s] _ _.
Arguments now_map [A B f P s] _.
Arguments now_map_conv [A B f P s] _.
Arguments next_map [A B f P Q] _ [s] _.
Arguments next_map_conv [A B f P Q] _ [s] _.
Arguments consecutive_map [A B f P s] _.
Arguments consecutive_map_conv [A B f P s] _.
Arguments always_map [A B f P Q] _ [s] _.
Arguments always_map_conv_ext [A B f P Q J] _ _ [s] _ _.
Arguments always_map_conv [A B f P Q] _ [s] _.
Arguments weak_until_map [A B f J P K Q] _ _ [s] _.
Arguments weak_until_map_conv [A B f J P K Q] _ _ [s] _.
Arguments until_map [A B f J P K Q] _ _ [s] _.
Arguments release_map [A B f J P K Q] _ _ [s] _.
Arguments release_map_conv [A B f J P K Q] _ _ [s] _.
Arguments eventually_map [A B f P Q] _ [s] _.
Arguments eventually_map_conv_ext [A B f P Q J] _ _ _ _ _ [s] _ _.
Arguments eventually_map_conv [A B f P Q] _ _ _ [s] _.
Arguments eventually_map_monotonic [A B f P Q] _ _ _ _ _ [s] _ _ _.
Arguments inf_often_map [A B f P Q] _ [s] _.
Arguments inf_often_map_conv [A B f P Q] _ _ _ [s] _.
Arguments continuously_map [A B f P Q] _ [s] _.
Arguments continuously_map_conv [A B f P Q] _ _ _ [s] _.
Arguments eventually_now_map [A B f P s] _.
Arguments eventually_now_map_conv [A B f P s] _.
Arguments eventually_map_now_eq [A B f a s] _.

Lemma map_Cons: forall (f:A->B) x s, map f (Cons x s) = Cons (f x) (map f s).
Proof using.
intros.
pattern (map f (Cons x s)).
rewrite <- recons.
simpl.
Admitted.

Lemma zip_Cons: forall (a:A) (b:B) sA sB, zip (Cons a sA) (Cons b sB) = Cons (a, b) (zip sA sB).
Proof using.
intros.
pattern (zip (Cons a sA) (Cons b sB)); rewrite <- recons.
simpl.
Admitted.

Lemma and_tl_map : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, P s -> Q (map f s)) -> (forall s, P' s -> Q' (map f s)) -> forall (s: infseq A), (P /\_ P') s -> (Q /\_ Q') (map f s).
Proof using.
Admitted.

Lemma and_tl_map_conv : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, Q (map f s) -> P s) -> (forall s, Q' (map f s) -> P' s) -> forall (s: infseq A), (Q /\_ Q') (map f s) -> (P /\_ P') s.
Proof using.
Admitted.

Lemma or_tl_map : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, P s -> Q (map f s)) -> (forall s, P' s -> Q' (map f s)) -> forall (s: infseq A), (P \/_ P') s -> (Q \/_ Q') (map f s).
Proof using.
Admitted.

Lemma or_tl_map_conv : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, Q (map f s) -> P s) -> (forall s, Q' (map f s) -> P' s) -> forall (s: infseq A), (Q \/_ Q') (map f s) -> (P \/_ P') s.
Proof using.
Admitted.

Lemma impl_tl_map : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, Q (map f s) -> P s) -> (forall s, P' s -> Q' (map f s)) -> forall (s: infseq A), (P ->_ P') s -> (Q ->_ Q') (map f s).
Proof using.
Admitted.

Lemma impl_tl_map_conv : forall (f: A->B) (P P': infseq A->Prop) (Q Q': infseq B->Prop), (forall s, P s -> Q (map f s)) -> (forall s, Q' (map f s) -> P' s) -> forall (s: infseq A), (Q ->_ Q') (map f s) -> (P ->_ P') s.
Proof using.
Admitted.

Lemma not_tl_map : forall (f: A->B) (P : infseq A->Prop) (Q: infseq B->Prop), (forall s, Q (map f s) -> P s) -> forall (s: infseq A), (~_ P) s -> (~_ Q) (map f s).
Proof using.
Admitted.

Lemma not_tl_map_conv : forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop), (forall s, P s -> Q (map f s)) -> forall (s: infseq A), (~_ Q) (map f s) -> (~_ P) s.
Proof using.
Admitted.

Lemma now_map_conv : forall (f: A->B) (P: B->Prop) (s: infseq A), now P (map f s) -> now (fun x => P (f x)) s.
Proof using.
Admitted.

Lemma next_map : forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop), (forall s, P s -> Q (map f s)) -> forall (s: infseq A), next P s -> next Q (map f s).
Proof using.
Admitted.

Lemma next_map_conv : forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop), (forall s, Q (map f s) -> P s) -> forall (s: infseq A), next Q (map f s) -> next P s.
Proof using.
Admitted.

Lemma consecutive_map : forall (f: A->B) (P: B->B->Prop) (s: infseq A), consecutive (fun x y => P (f x) (f y)) s -> consecutive P (map f s).
Proof using.
Admitted.

Lemma consecutive_map_conv : forall (f: A->B) (P: B->B->Prop) (s: infseq A), consecutive P (map f s) -> consecutive (fun x y => P (f x) (f y)) s.
Proof using.
Admitted.

Lemma always_map : forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop), (forall s, P s -> Q (map f s)) -> forall (s: infseq A), always P s -> always Q (map f s).
Proof using.
intros f P Q PQ.
cofix cf.
intros (x, s) a.
case (always_Cons a); intros a1 a2.
constructor.
-
apply PQ.
assumption.
-
rewrite map_Cons; simpl.
Admitted.

Lemma always_map_conv_ext : forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop) (J : infseq A -> Prop), (forall x s, J (Cons x s) -> J s) -> (forall s, J s -> Q (map f s) -> P s) -> forall s, J s -> always Q (map f s) -> always P s.
Proof using.
intros f J P Q inv JQP.
cofix c.
intros [x s] Js a.
rewrite map_Cons in a.
case (always_Cons a); intros a1 a2.
constructor.
-
apply JQP.
assumption.
rewrite map_Cons; assumption.
-
simpl.
apply c.
*
apply (inv x).
assumption.
*
Admitted.

Lemma always_map_conv : forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop), (forall s, Q (map f s) -> P s) -> forall (s: infseq A), always Q (map f s) -> always P s.
Proof using.
intros f P Q QP s.
Admitted.

Lemma weak_until_map : forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop), (forall s, J s -> K (map f s)) -> (forall s, P s -> Q (map f s)) -> forall (s: infseq A), weak_until J P s -> weak_until K Q (map f s).
Proof using.
intros f J P K Q JK PQ.
cofix cf.
intros (x, s) un.
case (weak_until_Cons un); clear un.
-
intro Pxs; constructor 1.
apply PQ.
assumption.
-
intros (Jxs, un).
rewrite map_Cons.
constructor 2.
*
rewrite <- map_Cons.
auto.
*
simpl.
Admitted.

Lemma weak_until_map_conv : forall (f: A->B) (J P: infseq A->Prop) (K Q: infseq B->Prop), (forall s, K (map f s) -> J s) -> (forall s, Q (map f s) -> P s) -> forall (s: infseq A), weak_until K Q (map f s) -> weak_until J P s.
Proof using.
intros f J P K Q KJ QP.
cofix cf.
intros (x, s) un.
rewrite map_Cons in un; case (weak_until_Cons un); clear un; rewrite <- map_Cons.
-
intro Qxs; constructor 1.
apply QP.
assumption.
-
intros (Kxs, un).
Admitted.

Lemma now_map : forall (f: A->B) (P: B->Prop) (s: infseq A), now (fun x => P (f x)) s -> now P (map f s).
Proof using.
intros f P (x, s) nP; assumption.
