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

Lemma eventually_map_conv_ext : forall (f: A->B) (P: infseq A->Prop) (Q: infseq B->Prop) (J : infseq A -> Prop), extensional P -> extensional Q -> extensional J -> (forall x s, J (Cons x s) -> J s) -> (forall s, J s -> Q (map f s) -> eventually P s) -> forall s, J s -> eventually Q (map f s) -> eventually P s.
Proof using.
intros f P Q J extP extQ extJ inv QP s Js ev.
revert Js.
assert (efst: J (map fstAB (zip s (map f s))) -> eventually P (map fstAB (zip s (map f s)))).
-
assert (evzip : eventually (fun sc => Q (map f (map fstAB sc))) (zip s (map f s))).
*
clear extP QP P.
assert (alzip : (always (now (fun c : A * B => let (x, y) := c in y = f x)) (zip s (map f s)))).
+
clear ev extQ.
generalize s.
cofix cf.
intros (x, s0).
constructor.
--
simpl.
reflexivity.
--
simpl.
apply cf.
+
apply (eventually_map_conv_aux f Q extQ s (map f s) alzip ev).
*
clear ev.
induction evzip as [((a, b), sAB) QabsAB | c sAB _ induc_hyp].
+
intros Js.
apply QP; assumption.
+
intros Js.
rewrite map_Cons.
apply E_next.
apply induc_hyp.
rewrite map_Cons in Js.
apply (inv (fstAB c)).
assumption.
-
intros Js.
assert (emJ: J (map fstAB (zip s (map f s)))).
*
unfold extensional in extJ.
apply (extJ s).
+
apply exteq_sym.
apply exteq_fst_zip.
+
assumption.
*
apply efst in emJ.
genclear emJ.
apply extensional_eventually.
+
exact extP.
+
apply exteq_fst_zip.
