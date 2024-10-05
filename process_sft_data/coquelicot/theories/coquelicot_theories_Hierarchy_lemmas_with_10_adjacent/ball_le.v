Require Import Reals mathcomp.ssreflect.ssreflect.
Require Import Rcomplements Rbar Markov Iter Lub.
Open Scope R_scope.
Class Filter {T : Type} (F : (T -> Prop) -> Prop) := { filter_true : F (fun _ => True) ; filter_and : forall P Q : T -> Prop, F P -> F Q -> F (fun x => P x /\ Q x) ; filter_imp : forall P Q : T -> Prop, (forall x, P x -> Q x) -> F P -> F Q }.
Global Hint Mode Filter + + : typeclass_instances.
Class ProperFilter' {T : Type} (F : (T -> Prop) -> Prop) := { filter_not_empty : not (F (fun _ => False)) ; filter_filter' :> Filter F }.
Class ProperFilter {T : Type} (F : (T -> Prop) -> Prop) := { filter_ex : forall P, F P -> exists x, P x ; filter_filter :> Filter F }.
Global Instance Proper_StrongProper : forall {T : Type} (F : (T -> Prop) -> Prop), ProperFilter F -> ProperFilter' F.
Proof.
intros T F [H1 H2].
constructor.
intros H.
now destruct (H1 _ H) as [x Hx].
exact H2.
Definition filter_le {T : Type} (F G : (T -> Prop) -> Prop) := forall P, G P -> F P.
Definition filtermap {T U : Type} (f : T -> U) (F : (T -> Prop) -> Prop) := fun P => F (fun x => P (f x)).
Global Instance filtermap_filter : forall T U (f : T -> U) (F : (T -> Prop) -> Prop), Filter F -> Filter (filtermap f F).
Proof.
intros T U f F FF.
unfold filtermap.
constructor.
-
apply filter_true.
-
intros P Q HP HQ.
now apply filter_and.
-
intros P Q H HP.
apply (filter_imp (fun x => P (f x))).
intros x Hx.
now apply H.
exact HP.
Global Instance filtermap_proper_filter' : forall T U (f : T -> U) (F : (T -> Prop) -> Prop), ProperFilter' F -> ProperFilter' (filtermap f F).
Proof.
intros T U f F FF.
unfold filtermap.
split.
-
apply filter_not_empty.
-
apply filtermap_filter.
apply filter_filter'.
Global Instance filtermap_proper_filter : forall T U (f : T -> U) (F : (T -> Prop) -> Prop), ProperFilter F -> ProperFilter (filtermap f F).
Proof.
intros T U f F FF.
unfold filtermap.
split.
-
intros P FP.
destruct (filter_ex _ FP) as [x Hx].
now exists (f x).
-
apply filtermap_filter.
apply filter_filter.
Definition filtermapi {T U : Type} (f : T -> U -> Prop) (F : (T -> Prop) -> Prop) := fun P : U -> Prop => F (fun x => exists y, f x y /\ P y).
Global Instance filtermapi_filter : forall T U (f : T -> U -> Prop) (F : (T -> Prop) -> Prop), F (fun x => (exists y, f x y) /\ forall y1 y2, f x y1 -> f x y2 -> y1 = y2) -> Filter F -> Filter (filtermapi f F).
Proof.
intros T U f F H FF.
unfold filtermapi.
constructor.
-
apply: filter_imp H => x [[y Hy] H].
exists y.
exact (conj Hy I).
-
intros P Q HP HQ.
apply: filter_imp (filter_and _ _ (filter_and _ _ HP HQ) H).
intros x [[[y1 [Hy1 Py]] [y2 [Hy2 Qy]]] [[y Hy] Hf]].
exists y.
apply (conj Hy).
split.
now rewrite (Hf y y1).
now rewrite (Hf y y2).
-
intros P Q HPQ HP.
apply: filter_imp HP.
intros x [y [Hf Py]].
exists y.
apply (conj Hf).
now apply HPQ.
Global Instance filtermapi_proper_filter' : forall T U (f : T -> U -> Prop) (F : (T -> Prop) -> Prop), F (fun x => (exists y, f x y) /\ forall y1 y2, f x y1 -> f x y2 -> y1 = y2) -> ProperFilter' F -> ProperFilter' (filtermapi f F).
Proof.
intros T U f F HF FF.
unfold filtermapi.
split.
-
intro H.
apply filter_not_empty.
apply filter_imp with (2 := H).
now intros x [y [_ Hy]].
-
apply filtermapi_filter.
exact HF.
apply filter_filter'.
Global Instance filtermapi_proper_filter : forall T U (f : T -> U -> Prop) (F : (T -> Prop) -> Prop), F (fun x => (exists y, f x y) /\ forall y1 y2, f x y1 -> f x y2 -> y1 = y2) -> ProperFilter F -> ProperFilter (filtermapi f F).
Proof.
intros T U f F HF FF.
unfold filtermapi.
split.
-
intros P FP.
destruct (filter_ex _ FP) as [x [y [_ Hy]]].
now exists y.
-
apply filtermapi_filter.
exact HF.
apply filter_filter.
Definition filterlim {T U : Type} (f : T -> U) F G := filter_le (filtermap f F) G.
Definition filterlimi {T U : Type} (f : T -> U -> Prop) F G := filter_le (filtermapi f F) G.
Inductive filter_prod {T U : Type} (F G : _ -> Prop) (P : T * U -> Prop) : Prop := Filter_prod (Q : T -> Prop) (R : U -> Prop) : F Q -> G R -> (forall x y, Q x -> R y -> P (x, y)) -> filter_prod F G P.
Global Instance filter_prod_filter : forall T U (F : (T -> Prop) -> Prop) (G : (U -> Prop) -> Prop), Filter F -> Filter G -> Filter (filter_prod F G).
Proof.
intros T U F G FF FG.
constructor.
-
exists (fun _ => True) (fun _ => True).
apply filter_true.
apply filter_true.
easy.
-
intros P Q [AP BP P1 P2 P3] [AQ BQ Q1 Q2 Q3].
exists (fun x => AP x /\ AQ x) (fun x => BP x /\ BQ x).
now apply filter_and.
now apply filter_and.
intros x y [Px Qx] [Py Qy].
split.
now apply P3.
now apply Q3.
-
intros P Q HI [AP BP P1 P2 P3].
exists AP BP ; try easy.
intros x y Hx Hy.
apply HI.
now apply P3.
Global Instance filter_prod_proper' {T1 T2 : Type} {F : (T1 -> Prop) -> Prop} {G : (T2 -> Prop) -> Prop} {FF : ProperFilter' F} {FG : ProperFilter' G} : ProperFilter' (filter_prod F G).
Proof.
split.
unfold not.
apply filter_prod_ind.
intros Q R HQ HR HQR.
apply filter_not_empty.
apply filter_imp with (2 := HR).
intros y Hy.
apply FF.
apply filter_imp with (2 := HQ).
intros x Hx.
now apply (HQR x y).
apply filter_prod_filter.
apply FF.
apply FG.
Global Instance filter_prod_proper {T1 T2 : Type} {F : (T1 -> Prop) -> Prop} {G : (T2 -> Prop) -> Prop} {FF : ProperFilter F} {FG : ProperFilter G} : ProperFilter (filter_prod F G).
Proof.
split.
intros P [Q1 Q2 H1 H2 HP].
case: (filter_ex _ H1) => x1 Hx1.
case: (filter_ex _ H2) => x2 Hx2.
exists (x1,x2).
by apply HP.
apply filter_prod_filter.
apply FF.
apply FG.
Definition within {T : Type} D (F : (T -> Prop) -> Prop) (P : T -> Prop) := F (fun x => D x -> P x).
Global Instance within_filter : forall T D F, Filter F -> Filter (@within T D F).
Proof.
intros T D F FF.
unfold within.
constructor.
-
now apply filter_forall.
-
intros P Q WP WQ.
apply filter_imp with (fun x => (D x -> P x) /\ (D x -> Q x)).
intros x [HP HQ] HD.
split.
now apply HP.
now apply HQ.
now apply filter_and.
-
intros P Q H FP.
apply filter_imp with (fun x => (D x -> P x) /\ (P x -> Q x)).
intros x [H1 H2] HD.
apply H2, H1, HD.
apply filter_and.
exact FP.
now apply filter_forall.
Definition subset_filter {T} (F : (T -> Prop) -> Prop) (dom : T -> Prop) (P : {x|dom x} -> Prop) : Prop := F (fun x => forall H : dom x, P (exist _ x H)).
Global Instance subset_filter_filter : forall T F (dom : T -> Prop), Filter F -> Filter (subset_filter F dom).
Proof.
intros T F dom FF.
constructor ; unfold subset_filter.
-
now apply filter_imp with (2 := filter_true).
-
intros P Q HP HQ.
generalize (filter_and _ _ HP HQ).
apply filter_imp.
intros x [H1 H2] H.
now split.
-
intros P Q H.
apply filter_imp.
intros x H' H0.
now apply H.
Module AbelianGroup.
Record mixin_of (G : Type) := Mixin { plus : G -> G -> G ; opp : G -> G ; zero : G ; ax1 : forall x y, plus x y = plus y x ; ax2 : forall x y z, plus x (plus y z) = plus (plus x y) z ; ax3 : forall x, plus x zero = x ; ax4 : forall x, plus x (opp x) = zero }.
Notation class_of := mixin_of (only parsing).
Section ClassDef.
Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Definition class (cT : type) := let: Pack _ c _ := cT return class_of cT in c.
End ClassDef.
Module Exports.
Coercion sort : type >-> Sortclass.
Notation AbelianGroup := type.
End Exports.
End AbelianGroup.
Export AbelianGroup.Exports.
Section AbelianGroup1.
Context {G : AbelianGroup}.
Definition zero := AbelianGroup.zero _ (AbelianGroup.class G).
Definition plus := AbelianGroup.plus _ (AbelianGroup.class G).
Definition opp := AbelianGroup.opp _ (AbelianGroup.class G).
Definition minus x y := (plus x (opp y)).
End AbelianGroup1.
Section Sums.
Context {G : AbelianGroup}.
Definition sum_n_m (a : nat -> G) n m := iter_nat plus zero a n m.
Definition sum_n (a : nat -> G) n := sum_n_m a O n.
End Sums.
Module Ring.
Record mixin_of (K : AbelianGroup) := Mixin { mult : K -> K -> K ; one : K ; ax1 : forall x y z, mult x (mult y z) = mult (mult x y) z ; ax2 : forall x, mult x one = x ; ax3 : forall x, mult one x = x ; ax4 : forall x y z, mult (plus x y) z = plus (mult x z) (mult y z) ; ax5 : forall x y z, mult x (plus y z) = plus (mult x y) (mult x z) }.
Section ClassDef.
Record class_of (K : Type) := Class { base : AbelianGroup.class_of K ; mixin : mixin_of (AbelianGroup.Pack _ base K) }.
Local Coercion base : class_of >-> AbelianGroup.class_of.
Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variable cT : type.
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
End ClassDef.
Module Exports.
Coercion base : class_of >-> AbelianGroup.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Notation Ring := type.
End Exports.
End Ring.
Export Ring.Exports.
Section Ring1.
Context {K : Ring}.
Definition mult : K -> K -> K := Ring.mult _ (Ring.class K).
Definition one : K := Ring.one _ (Ring.class K).
Fixpoint pow_n (x : K) (N : nat) {struct N} : K := match N with | 0%nat => one | S i => mult x (pow_n x i) end.
End Ring1.
Module AbsRing.
Record mixin_of (K : Ring) := Mixin { abs : K -> R ; ax1 : abs zero = 0 ; ax2 : abs (opp one) = 1 ; ax3 : forall x y : K, abs (plus x y) <= abs x + abs y ; ax4 : forall x y : K, abs (mult x y) <= abs x * abs y ; ax5 : forall x : K, abs x = 0 -> x = zero }.
Section ClassDef.
Record class_of (K : Type) := Class { base : Ring.class_of K ; mixin : mixin_of (Ring.Pack _ base K) }.
Local Coercion base : class_of >-> Ring.class_of.
Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variable cT : type.
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition Ring := Ring.Pack cT xclass xT.
End ClassDef.
Module Exports.
Coercion base : class_of >-> Ring.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion Ring : type >-> Ring.type.
Canonical Ring.
Notation AbsRing := type.
End Exports.
End AbsRing.
Export AbsRing.Exports.
Section AbsRing1.
Context {K : AbsRing}.
Definition abs : K -> R := AbsRing.abs _ (AbsRing.class K).
End AbsRing1.
Module UniformSpace.
Record mixin_of (M : Type) := Mixin { ball : M -> R -> M -> Prop ; ax1 : forall x (e : posreal), ball x e x ; ax2 : forall x y e, ball x e y -> ball y e x ; ax3 : forall x y z e1 e2, ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z }.
Notation class_of := mixin_of (only parsing).
Section ClassDef.
Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Definition class (cT : type) := let: Pack _ c _ := cT return class_of cT in c.
End ClassDef.
Module Exports.
Coercion sort : type >-> Sortclass.
Notation UniformSpace := type.
End Exports.
End UniformSpace.
Export UniformSpace.Exports.
Section UniformSpace1.
Context {M : UniformSpace}.
Definition ball := UniformSpace.ball _ (UniformSpace.class M).
Definition close (x y : M) : Prop := forall eps : posreal, ball x eps y.
End UniformSpace1.
Section AbsRing_UniformSpace.
Variable K : AbsRing.
Definition AbsRing_ball (x : K) (eps : R) (y : K) := abs (minus y x) < eps.
Definition AbsRing_UniformSpace_mixin := UniformSpace.Mixin _ _ AbsRing_ball_center AbsRing_ball_sym AbsRing_ball_triangle.
Canonical AbsRing_UniformSpace := UniformSpace.Pack K AbsRing_UniformSpace_mixin K.
End AbsRing_UniformSpace.
Section fct_UniformSpace.
Variable (T : Type) (U : UniformSpace).
Definition fct_ball (x : T -> U) (eps : R) (y : T -> U) := forall t : T, ball (x t) eps (y t).
Definition fct_UniformSpace_mixin := UniformSpace.Mixin _ _ fct_ball_center fct_ball_sym fct_ball_triangle.
Canonical fct_UniformSpace := UniformSpace.Pack (T -> U) fct_UniformSpace_mixin (T -> U).
End fct_UniformSpace.
Definition locally_dist {T : Type} (d : T -> R) (P : T -> Prop) := exists delta : posreal, forall y, d y < delta -> P y.
Global Instance locally_dist_filter : forall T (d : T -> R), Filter (locally_dist d).
Proof.
intros T d.
constructor.
-
now exists (mkposreal _ Rlt_0_1).
-
intros P Q [dP HP] [dQ HQ].
exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
simpl.
intros y Hy.
split.
apply HP.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_l.
apply HQ.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
-
intros P Q H [dP HP].
exists dP.
intros y Hy.
apply H.
now apply HP.
Section Locally.
Context {T : UniformSpace}.
Definition locally (x : T) (P : T -> Prop) := exists eps : posreal, forall y, ball x eps y -> P y.
Global Instance locally_filter : forall x : T, ProperFilter (locally x).
Proof.
intros x.
constructor ; [idtac|constructor].
-
intros P [eps H].
exists x.
apply H.
apply ball_center.
-
now exists (mkposreal _ Rlt_0_1).
-
intros P Q [dP HP] [dQ HQ].
exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
simpl.
intros y Hy.
split.
apply HP.
apply ball_le with (2 := Hy).
apply Rmin_l.
apply HQ.
apply ball_le with (2 := Hy).
apply Rmin_r.
-
intros P Q H [dP HP].
exists dP.
intros y Hy.
apply H.
now apply HP.
Definition is_filter_lim (F : (T -> Prop) -> Prop) (x : T) := forall P, locally x P -> F P.
End Locally.
Section Locally_fct.
Context {T : Type} {U : UniformSpace}.
End Locally_fct.
Definition locally' {T : UniformSpace} (x : T) := within (fun y => y <> x) (locally x).
Global Instance locally'_filter : forall {T : UniformSpace} (x : T), Filter (locally' x).
Proof.
intros T x.
apply within_filter.
apply locally_filter.
Section at_point.
Context {T : UniformSpace}.
Definition at_point (a : T) (P : T -> Prop) : Prop := P a.
Global Instance at_point_filter (a : T) : ProperFilter (at_point a).
Proof.
split.
-
intros P Pa.
now exists a.
-
split ; try easy.
intros P Q PQ Ha.
now apply PQ.
End at_point.
Section Open.
Context {T : UniformSpace}.
Definition open (D : T -> Prop) := forall x, D x -> locally x D.
End Open.
Section Closed.
Context {T : UniformSpace}.
Definition closed (D : T -> Prop) := forall x, not (locally x (fun x : T => not (D x))) -> D x.
End Closed.
Definition cauchy {T : UniformSpace} (F : (T -> Prop) -> Prop) := forall eps : posreal, exists x, F (ball x eps).
Module CompleteSpace.
Record mixin_of (T : UniformSpace) := Mixin { lim : ((T -> Prop) -> Prop) -> T ; ax1 : forall F, ProperFilter F -> cauchy F -> forall eps : posreal, F (ball (lim F) eps) ; ax2 : forall F1 F2, filter_le F1 F2 -> filter_le F2 F1 -> close (lim F1) (lim F2) }.
Section ClassDef.
Record class_of (T : Type) := Class { base : UniformSpace.class_of T ; mixin : mixin_of (UniformSpace.Pack _ base T) }.
Local Coercion base : class_of >-> UniformSpace.class_of.
Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variable cT : type.
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition UniformSpace := UniformSpace.Pack cT xclass xT.
End ClassDef.
Module Exports.
Coercion base : class_of >-> UniformSpace.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Notation CompleteSpace := type.
End Exports.
End CompleteSpace.
Export CompleteSpace.Exports.
Section CompleteSpace1.
Context {T : CompleteSpace}.
Definition lim : ((T -> Prop) -> Prop) -> T := CompleteSpace.lim _ (CompleteSpace.class T).
Definition iota (P : T -> Prop) := lim (fun A => (forall x, P x -> A x)).
End CompleteSpace1.
Section fct_CompleteSpace.
Context {T : Type} {U : CompleteSpace}.
Definition lim_fct (F : ((T -> U) -> Prop) -> Prop) (t : T) := lim (fun P => F (fun g => P (g t))).
Definition fct_CompleteSpace_mixin := CompleteSpace.Mixin _ lim_fct complete_cauchy_fct close_lim_fct.
Canonical fct_CompleteSpace := CompleteSpace.Pack (T -> U) (CompleteSpace.Class _ _ fct_CompleteSpace_mixin) (T -> U).
End fct_CompleteSpace.
Section Filterlim_switch.
Context {T1 T2 : Type}.
End Filterlim_switch.
Module ModuleSpace.
Record mixin_of (K : Ring) (V : AbelianGroup) := Mixin { scal : K -> V -> V ; ax1 : forall x y u, scal x (scal y u) = scal (mult x y) u ; ax2 : forall u, scal one u = u ; ax3 : forall x u v, scal x (plus u v) = plus (scal x u) (scal x v) ; ax4 : forall x y u, scal (plus x y) u = plus (scal x u) (scal y u) }.
Section ClassDef.
Variable K : Ring.
Record class_of (V : Type) := Class { base : AbelianGroup.class_of V ; mixin : mixin_of K (AbelianGroup.Pack _ base V) }.
Local Coercion base : class_of >-> AbelianGroup.class_of.
Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variable cT : type.
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
End ClassDef.
Module Exports.
Coercion base : class_of >-> AbelianGroup.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Notation ModuleSpace := type.
End Exports.
End ModuleSpace.
Export ModuleSpace.Exports.
Section ModuleSpace1.
Context {K : Ring} {V : ModuleSpace K}.
Definition scal : K -> V -> V := ModuleSpace.scal _ _ (ModuleSpace.class K V).
End ModuleSpace1.
Section Ring_ModuleSpace.
Variable (K : Ring).
Definition Ring_ModuleSpace_mixin := ModuleSpace.Mixin K _ _ mult_assoc mult_one_l mult_distr_l mult_distr_r.
Canonical Ring_ModuleSpace := ModuleSpace.Pack K K (ModuleSpace.Class _ _ _ Ring_ModuleSpace_mixin) K.
End Ring_ModuleSpace.
Section AbsRing_ModuleSpace.
Variable (K : AbsRing).
Definition AbsRing_ModuleSpace_mixin := ModuleSpace.Mixin K _ _ mult_assoc mult_one_l mult_distr_l mult_distr_r.
Canonical AbsRing_ModuleSpace := ModuleSpace.Pack K K (ModuleSpace.Class _ _ _ AbsRing_ModuleSpace_mixin) K.
End AbsRing_ModuleSpace.
Module NormedModuleAux.
Section ClassDef.
Variable K : AbsRing.
Record class_of (T : Type) := Class { base : ModuleSpace.class_of K T ; mixin : UniformSpace.mixin_of T }.
Local Coercion base : class_of >-> ModuleSpace.class_of.
Local Coercion mixin : class_of >-> UniformSpace.class_of.
Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variable cT : type.
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition UniformSpace := UniformSpace.Pack cT xclass xT.
End ClassDef.
Module Exports.
Coercion base : class_of >-> ModuleSpace.class_of.
Coercion mixin : class_of >-> UniformSpace.class_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Notation NormedModuleAux := type.
End Exports.
End NormedModuleAux.
Export NormedModuleAux.Exports.
Module NormedModule.
Record mixin_of (K : AbsRing) (V : NormedModuleAux K) := Mixin { norm : V -> R ; norm_factor : R ; ax1 : forall (x y : V), norm (plus x y) <= norm x + norm y ; ax2 : forall (l : K) (x : V), norm (scal l x) <= abs l * norm x ; ax3 : forall (x y : V) (eps : R), norm (minus y x) < eps -> ball x eps y ; ax4 : forall (x y : V) (eps : posreal), ball x eps y -> norm (minus y x) < norm_factor * eps ; ax5 : forall x : V, norm x = 0 -> x = zero }.
Section ClassDef.
Variable K : AbsRing.
Record class_of (T : Type) := Class { base : NormedModuleAux.class_of K T ; mixin : mixin_of K (NormedModuleAux.Pack K T base T) }.
Local Coercion base : class_of >-> NormedModuleAux.class_of.
Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variable cT : type.
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition UniformSpace := UniformSpace.Pack cT xclass xT.
Definition NormedModuleAux := NormedModuleAux.Pack _ cT xclass xT.
End ClassDef.
Module Exports.
Coercion base : class_of >-> NormedModuleAux.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Coercion NormedModuleAux : type >-> NormedModuleAux.type.
Canonical NormedModuleAux.
Notation NormedModule := type.
End Exports.
End NormedModule.
Export NormedModule.Exports.
Section NormedModule1.
Context {K : AbsRing} {V : NormedModule K}.
Definition norm : V -> R := NormedModule.norm K _ (NormedModule.class K V).
Definition norm_factor : R := NormedModule.norm_factor K _ (NormedModule.class K V).
Definition ball_norm (x : V) (eps : R) (y : V) := norm (minus y x) < eps.
Definition locally_norm (x : V) (P : V -> Prop) := exists eps : posreal, forall y, ball_norm x eps y -> P y.
End NormedModule1.
Section NormedModule2.
Context {T : Type} {K : AbsRing} {V : NormedModule K}.
End NormedModule2.
Section AbsRing_NormedModule.
Variable (K : AbsRing).
Canonical AbsRing_NormedModuleAux := NormedModuleAux.Pack K K (NormedModuleAux.Class _ _ (ModuleSpace.class _ (AbsRing_ModuleSpace K)) (UniformSpace.class (AbsRing_UniformSpace K))) K.
Definition AbsRing_NormedModule_mixin := NormedModule.Mixin K _ abs 1 abs_triangle abs_mult (fun x y e H => H) AbsRing_norm_compat2 abs_eq_zero.
Canonical AbsRing_NormedModule := NormedModule.Pack K _ (NormedModule.Class _ _ _ AbsRing_NormedModule_mixin) K.
End AbsRing_NormedModule.
Section NVS_continuity.
Context {K : AbsRing} {V : NormedModule K}.
End NVS_continuity.
Module CompleteNormedModule.
Section ClassDef.
Variable K : AbsRing.
Record class_of (T : Type) := Class { base : NormedModule.class_of K T ; mixin : CompleteSpace.mixin_of (UniformSpace.Pack T base T) }.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : CompleteSpace.class_of T := CompleteSpace.Class _ (base T cT) (mixin T cT).
Local Coercion base2 : class_of >-> CompleteSpace.class_of.
Structure type := Pack { sort; _ : class_of sort ; _ : Type }.
Local Coercion sort : type >-> Sortclass.
Variable cT : type.
Definition class := let: Pack _ c _ := cT return class_of cT in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition AbelianGroup := AbelianGroup.Pack cT xclass xT.
Definition ModuleSpace := ModuleSpace.Pack _ cT xclass xT.
Definition NormedModuleAux := NormedModuleAux.Pack _ cT xclass xT.
Definition NormedModule := NormedModule.Pack _ cT xclass xT.
Definition UniformSpace := UniformSpace.Pack cT xclass xT.
Definition CompleteSpace := CompleteSpace.Pack cT xclass xT.
End ClassDef.
Module Exports.
Coercion base : class_of >-> NormedModule.class_of.
Coercion mixin : class_of >-> CompleteSpace.mixin_of.
Coercion base2 : class_of >-> CompleteSpace.class_of.
Coercion sort : type >-> Sortclass.
Coercion AbelianGroup : type >-> AbelianGroup.type.
Canonical AbelianGroup.
Coercion ModuleSpace : type >-> ModuleSpace.type.
Canonical ModuleSpace.
Coercion NormedModuleAux : type >-> NormedModuleAux.type.
Canonical NormedModuleAux.
Coercion NormedModule : type >-> NormedModule.type.
Canonical NormedModule.
Coercion UniformSpace : type >-> UniformSpace.type.
Canonical UniformSpace.
Coercion CompleteSpace : type >-> CompleteSpace.type.
Canonical CompleteSpace.
Notation CompleteNormedModule := type.
End Exports.
End CompleteNormedModule.
Export CompleteNormedModule.Exports.
Section CompleteNormedModule1.
Context {K : AbsRing} {V : CompleteNormedModule K}.
Context {T : Type}.
End CompleteNormedModule1.
Section prod_AbelianGroup.
Context {U V : AbelianGroup}.
Definition prod_plus (x y : U * V) := (plus (fst x) (fst y), plus (snd x) (snd y)).
Definition prod_opp (x : U * V) := (opp (fst x), opp (snd x)).
Definition prod_zero : U * V := (zero, zero).
End prod_AbelianGroup.
Definition prod_AbelianGroup_mixin (U V : AbelianGroup) := AbelianGroup.Mixin (U * V) _ _ _ prod_plus_comm prod_plus_assoc prod_plus_zero_r prod_plus_opp_r.
Canonical prod_AbelianGroup (U V : AbelianGroup) := AbelianGroup.Pack (U * V) (prod_AbelianGroup_mixin U V) (U * V).
Section prod_UniformSpace.
Context {U V : UniformSpace}.
Definition prod_ball (x : U * V) (eps : R) (y : U * V) := ball (fst x) eps (fst y) /\ ball (snd x) eps (snd y).
End prod_UniformSpace.
Definition prod_UniformSpace_mixin (U V : UniformSpace) := UniformSpace.Mixin (U * V) _ prod_ball_center prod_ball_sym prod_ball_triangle.
Canonical prod_UniformSpace (U V : UniformSpace) := UniformSpace.Pack (U * V) (prod_UniformSpace_mixin U V) (U * V).
Section prod_ModuleSpace.
Context {K : Ring} {U V : ModuleSpace K}.
Definition prod_scal (x : K) (u : U * V) := (scal x (fst u), scal x (snd u)).
End prod_ModuleSpace.
Definition prod_ModuleSpace_mixin (K : Ring) (U V : ModuleSpace K) := ModuleSpace.Mixin K _ _ (@prod_scal_assoc K U V) prod_scal_one prod_scal_distr_l prod_scal_distr_r.
Canonical prod_ModuleSpace (K : Ring) (U V : ModuleSpace K) := ModuleSpace.Pack K (U * V) (ModuleSpace.Class _ _ _ (prod_ModuleSpace_mixin K U V)) (U * V).
Canonical prod_NormedModuleAux (K : AbsRing) (U V : NormedModuleAux K) := NormedModuleAux.Pack K (U * V) (NormedModuleAux.Class _ _ (ModuleSpace.class K _) (UniformSpace.class (prod_UniformSpace U V))) (U * V).
Section prod_NormedModule.
Context {K : AbsRing} {U V : NormedModule K}.
Definition prod_norm (x : U * V) := sqrt (norm (fst x) ^ 2 + norm (snd x) ^ 2).
Definition prod_norm_factor := sqrt 2 * Rmax (@norm_factor K U) (@norm_factor K V).
End prod_NormedModule.
Definition prod_NormedModule_mixin (K : AbsRing) (U V : NormedModule K) := NormedModule.Mixin K _ (@prod_norm K U V) prod_norm_factor prod_norm_triangle prod_norm_scal prod_norm_compat1 prod_norm_compat2 prod_norm_eq_zero.
Canonical prod_NormedModule (K : AbsRing) (U V : NormedModule K) := NormedModule.Pack K (U * V) (NormedModule.Class K (U * V) _ (prod_NormedModule_mixin K U V)) (U * V).
Fixpoint Tn (n : nat) (T : Type) : Type := match n with | O => unit | S n => prod T (Tn n T) end.
Notation "[ x1 , .. , xn ]" := (pair x1 .. (pair xn tt) .. ).
Fixpoint mk_Tn {T} (n : nat) (u : nat -> T) : Tn n T := match n with | O => (tt : Tn O T) | S n => (u O, mk_Tn n (fun n => u (S n))) end.
Fixpoint coeff_Tn {T} {n : nat} (x0 : T) : (Tn n T) -> nat -> T := match n with | O => fun (_ : Tn O T) (_ : nat) => x0 | S n' => fun (v : Tn (S n') T) (i : nat) => match i with | O => fst v | S i => coeff_Tn x0 (snd v) i end end.
Fixpoint Fn (n : nat) (T U : Type) : Type := match n with | O => U | S n => T -> Fn n T U end.
Section Matrices.
Context {T : Type}.
Definition matrix (m n : nat) := Tn m (Tn n T).
Definition coeff_mat {m n : nat} (x0 : T) (A : matrix m n) (i j : nat) := coeff_Tn x0 (coeff_Tn (mk_Tn _ (fun _ => x0)) A i) j.
Definition mk_matrix (m n : nat) (U : nat -> nat -> T) : matrix m n := mk_Tn m (fun i => (mk_Tn n (U i))).
End Matrices.
Section MatrixGroup.
Context {G : AbelianGroup} {m n : nat}.
Definition Mzero := mk_matrix m n (fun i j => @zero G).
Definition Mplus (A B : @matrix G m n) := mk_matrix m n (fun i j => plus (coeff_mat zero A i j) (coeff_mat zero B i j)).
Definition Mopp (A : @matrix G m n) := mk_matrix m n (fun i j => opp (coeff_mat zero A i j)).
Definition matrix_AbelianGroup_mixin := AbelianGroup.Mixin _ _ _ _ Mplus_comm Mplus_assoc Mplus_zero_r Mplus_opp_r.
Canonical matrix_AbelianGroup := AbelianGroup.Pack _ matrix_AbelianGroup_mixin (@matrix G m n).
End MatrixGroup.
Section MatrixRing.
Context {T : Ring}.
Fixpoint Mone_seq i j : T := match i,j with | O, O => one | O, S _ | S _, O => zero | S i, S j => Mone_seq i j end.
Definition Mone {n} : matrix n n := mk_matrix n n Mone_seq.
Definition Mmult {n m k} (A : @matrix T n m) (B : @matrix T m k) := mk_matrix n k (fun i j => sum_n (fun l => mult (coeff_mat zero A i l) (coeff_mat zero B l j)) (pred m)).
Definition matrix_Ring_mixin {n} := Ring.Mixin _ _ _ (@Mmult_assoc n n n n) Mmult_one_r Mmult_one_l Mmult_distr_r Mmult_distr_l.
Canonical matrix_Ring {n} := Ring.Pack (@matrix T n n) (Ring.Class _ _ matrix_Ring_mixin) (@matrix T n n).
Definition matrix_ModuleSpace_mixin {m n} := ModuleSpace.Mixin (@matrix_Ring m) (@matrix_AbelianGroup T m n) Mmult Mmult_assoc Mmult_one_l Mmult_distr_l Mmult_distr_r.
Canonical matrix_ModuleSpace {m n} := ModuleSpace.Pack _ (@matrix T m n) (ModuleSpace.Class _ _ _ matrix_ModuleSpace_mixin) (@matrix T m n).
End MatrixRing.
Definition eventually (P : nat -> Prop) := exists N : nat, forall n, (N <= n)%nat -> P n.
Global Instance eventually_filter : ProperFilter eventually.
Proof.
constructor.
intros P [N H].
exists N.
apply H.
apply le_refl.
constructor.
-
now exists 0%nat.
-
intros P Q [NP HP] [NQ HQ].
exists (max NP NQ).
intros n Hn.
split.
apply HP.
apply le_trans with (2 := Hn).
apply Max.le_max_l.
apply HQ.
apply le_trans with (2 := Hn).
apply Max.le_max_r.
-
intros P Q H [NP HP].
exists NP.
intros n Hn.
apply H.
now apply HP.
Definition R_AbelianGroup_mixin := AbelianGroup.Mixin _ _ _ _ Rplus_comm (fun x y z => sym_eq (Rplus_assoc x y z)) Rplus_0_r Rplus_opp_r.
Canonical R_AbelianGroup := AbelianGroup.Pack _ R_AbelianGroup_mixin R.
Definition R_Ring_mixin := Ring.Mixin _ _ _ (fun x y z => sym_eq (Rmult_assoc x y z)) Rmult_1_r Rmult_1_l Rmult_plus_distr_r Rmult_plus_distr_l.
Canonical R_Ring := Ring.Pack R (Ring.Class _ _ R_Ring_mixin) R.
Definition R_AbsRing_mixin := AbsRing.Mixin _ _ Rabs_R0 Rabs_m1 Rabs_triang (fun x y => Req_le _ _ (Rabs_mult x y)) Rabs_eq_0.
Canonical R_AbsRing := AbsRing.Pack R (AbsRing.Class _ _ R_AbsRing_mixin) R.
Definition R_UniformSpace_mixin := AbsRing_UniformSpace_mixin R_AbsRing.
Canonical R_UniformSpace := UniformSpace.Pack R R_UniformSpace_mixin R.
Definition R_complete_lim (F : (R -> Prop) -> Prop) : R := Lub_Rbar (fun x : R => F (ball (x + 1) (mkposreal _ Rlt_0_1))).
Definition R_CompleteSpace_mixin := CompleteSpace.Mixin _ R_complete_lim R_complete R_complete_close.
Canonical R_CompleteSpace := CompleteSpace.Pack R (CompleteSpace.Class _ _ R_CompleteSpace_mixin) R.
Definition R_ModuleSpace_mixin := AbsRing_ModuleSpace_mixin R_AbsRing.
Canonical R_ModuleSpace := ModuleSpace.Pack _ R (ModuleSpace.Class _ _ _ R_ModuleSpace_mixin) R.
Canonical R_NormedModuleAux := NormedModuleAux.Pack _ R (NormedModuleAux.Class _ _ (ModuleSpace.class _ R_ModuleSpace) (UniformSpace.class R_UniformSpace)) R.
Definition R_NormedModule_mixin := AbsRing_NormedModule_mixin R_AbsRing.
Canonical R_NormedModule := NormedModule.Pack _ R (NormedModule.Class _ _ _ R_NormedModule_mixin) R.
Canonical R_CompleteNormedModule := CompleteNormedModule.Pack _ R (CompleteNormedModule.Class R_AbsRing _ (NormedModule.class _ R_NormedModule) R_CompleteSpace_mixin) R.
Definition at_left x := within (fun u : R => Rlt u x) (locally x).
Definition at_right x := within (fun u : R => Rlt x u) (locally x).
Global Instance at_right_proper_filter : forall (x : R), ProperFilter (at_right x).
Proof.
constructor.
intros P [d Hd].
exists (x + d / 2).
apply Hd.
apply @norm_compat1 ; rewrite /norm /minus /plus /opp /= /abs /=.
ring_simplify (x + d / 2 + - x).
rewrite Rabs_pos_eq.
apply Rlt_div_l.
by apply Rlt_0_2.
apply Rminus_lt_0 ; ring_simplify ; by apply d.
apply Rlt_le, is_pos_div_2.
apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
apply within_filter, locally_filter.
Global Instance at_left_proper_filter : forall (x : R), ProperFilter (at_left x).
Proof.
constructor.
intros P [d Hd].
exists (x - d / 2).
apply Hd.
apply @norm_compat1 ; rewrite /norm /minus /plus /opp /= /abs /=.
ring_simplify (x - d / 2 + - x).
rewrite Rabs_Ropp Rabs_pos_eq.
apply Rlt_div_l.
by apply Rlt_0_2.
apply Rminus_lt_0 ; ring_simplify ; by apply d.
apply Rlt_le, is_pos_div_2.
apply Rminus_lt_0 ; ring_simplify ; by apply is_pos_div_2.
apply within_filter, locally_filter.
Definition locally_2d (P : R -> R -> Prop) x y := exists delta : posreal, forall u v, Rabs (u - x) < delta -> Rabs (v - y) < delta -> P u v.
Definition Rbar_locally' (a : Rbar) (P : R -> Prop) := match a with | Finite a => locally' a P | p_infty => exists M : R, forall x, M < x -> P x | m_infty => exists M : R, forall x, x < M -> P x end.
Definition Rbar_locally (a : Rbar) (P : R -> Prop) := match a with | Finite a => locally a P | p_infty => exists M : R, forall x, M < x -> P x | m_infty => exists M : R, forall x, x < M -> P x end.
Global Instance Rbar_locally'_filter : forall x, ProperFilter (Rbar_locally' x).
Proof.
intros [x| |] ; (constructor ; [idtac | constructor]).
-
intros P [eps HP].
exists (x + eps / 2).
apply HP.
rewrite /ball /= /AbsRing_ball /abs /minus /plus /opp /=.
ring_simplify (x + eps / 2 + - x).
rewrite Rabs_pos_eq.
apply Rminus_lt_0.
replace (eps - eps / 2) with (eps / 2) by field.
apply is_pos_div_2.
apply Rlt_le, is_pos_div_2.
apply Rgt_not_eq, Rminus_lt_0 ; ring_simplify.
apply is_pos_div_2.
-
now exists (mkposreal _ Rlt_0_1).
-
intros P Q [dP HP] [dQ HQ].
exists (mkposreal _ (Rmin_stable_in_posreal dP dQ)).
simpl.
intros y Hy H.
split.
apply HP with (2 := H).
apply Rlt_le_trans with (1 := Hy).
apply Rmin_l.
apply HQ with (2 := H).
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
-
intros P Q H [dP HP].
exists dP.
intros y Hy H'.
apply H.
now apply HP.
-
intros P [N HP].
exists (N + 1).
apply HP.
apply Rlt_plus_1.
-
now exists 0.
-
intros P Q [MP HP] [MQ HQ].
exists (Rmax MP MQ).
intros y Hy.
split.
apply HP.
apply Rle_lt_trans with (2 := Hy).
apply Rmax_l.
apply HQ.
apply Rle_lt_trans with (2 := Hy).
apply Rmax_r.
-
intros P Q H [dP HP].
exists dP.
intros y Hy.
apply H.
now apply HP.
-
intros P [N HP].
exists (N - 1).
apply HP.
apply Rlt_minus_l, Rlt_plus_1.
-
now exists 0.
-
intros P Q [MP HP] [MQ HQ].
exists (Rmin MP MQ).
intros y Hy.
split.
apply HP.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_l.
apply HQ.
apply Rlt_le_trans with (1 := Hy).
apply Rmin_r.
-
intros P Q H [dP HP].
exists dP.
intros y Hy.
apply H.
now apply HP.
Global Instance Rbar_locally_filter : forall x, ProperFilter (Rbar_locally x).
Proof.
intros [x| |].
-
apply locally_filter.
-
exact (Rbar_locally'_filter p_infty).
-
exact (Rbar_locally'_filter m_infty).
Definition Rbar_loc_seq (x : Rbar) (n : nat) := match x with | Finite x => x + / (INR n + 1) | p_infty => INR n | m_infty => - INR n end.

Lemma abs_mult : forall x y : K, abs (mult x y) <= abs x * abs y.
Proof.
Admitted.

Lemma abs_eq_zero : forall x : K, abs x = 0 -> x = zero.
Proof.
Admitted.

Lemma abs_opp : forall x, abs (opp x) = abs x.
Proof.
intros x.
apply Rle_antisym.
-
rewrite opp_mult_m1.
rewrite -(Rmult_1_l (abs x)) -abs_opp_one.
apply abs_mult.
-
rewrite -{1}[x]opp_opp.
rewrite opp_mult_m1.
rewrite -(Rmult_1_l (abs (opp x))) -abs_opp_one.
Admitted.

Lemma abs_minus : forall x y : K, abs (minus x y) = abs (minus y x).
Proof.
intros x y.
Admitted.

Lemma abs_one : abs one = 1.
Proof.
rewrite -abs_opp.
Admitted.

Lemma abs_ge_0 : forall x, 0 <= abs x.
Proof.
intros x.
apply Rmult_le_reg_l with 2.
by apply Rlt_0_2.
rewrite Rmult_0_r -abs_zero -(plus_opp_l x).
apply Rle_trans with (1 := abs_triangle _ _).
rewrite abs_opp.
Admitted.

Lemma abs_pow_n : forall (x : K) n, abs (pow_n x n) <= (abs x)^n.
Proof.
induction n.
apply Req_le, abs_one.
simpl.
apply: Rle_trans (abs_mult _ _) _.
apply Rmult_le_compat_l with (2 := IHn).
Admitted.

Lemma ball_center : forall (x : M) (e : posreal), ball x e x.
Proof.
Admitted.

Lemma ball_sym : forall (x y : M) (e : R), ball x e y -> ball y e x.
Proof.
Admitted.

Lemma ball_triangle : forall (x y z : M) (e1 e2 : R), ball x e1 y -> ball y e2 z -> ball x (e1 + e2) z.
Proof.
Admitted.

Lemma close_refl (x : M) : close x x.
Proof.
intros eps.
Admitted.

Lemma close_sym (x y : M) : close x y -> close y x.
Proof.
intros H eps.
Admitted.

Lemma close_trans (x y z : M) : close x y -> close y z -> close x z.
Proof.
intros H1 H2 eps.
rewrite (double_var eps) -[eps / 2]/(pos (pos_div_2 eps)).
Admitted.

Lemma AbsRing_ball_center : forall (x : K) (e : posreal), AbsRing_ball x e x.
Proof.
intros x e.
rewrite /AbsRing_ball /minus plus_opp_r abs_zero.
Admitted.

Lemma AbsRing_ball_sym : forall (x y : K) (e : R), AbsRing_ball x e y -> AbsRing_ball y e x.
Proof.
intros x y e.
Admitted.

Lemma AbsRing_ball_triangle : forall (x y z : K) (e1 e2 : R), AbsRing_ball x e1 y -> AbsRing_ball y e2 z -> AbsRing_ball x (e1 + e2) z.
Proof.
intros x y z e1 e2 H1 H2.
unfold AbsRing_ball.
replace (minus z x) with (plus (minus y x) (minus z y)).
apply: Rle_lt_trans (abs_triangle _ _) _.
now apply Rplus_lt_compat.
rewrite plus_comm /minus plus_assoc.
apply (f_equal (fun y => plus y _)).
rewrite <- plus_assoc.
Admitted.

Lemma fct_ball_center : forall (x : T -> U) (e : posreal), fct_ball x e x.
Proof.
intros x e t.
Admitted.

Lemma fct_ball_sym : forall (x y : T -> U) (e : R), fct_ball x e y -> fct_ball y e x.
Proof.
intros x y e H t.
Admitted.

Lemma fct_ball_triangle : forall (x y z : T -> U) (e1 e2 : R), fct_ball x e1 y -> fct_ball y e2 z -> fct_ball x (e1 + e2) z.
Proof.
intros x y z e1 e2 H1 H2 t.
Admitted.

Lemma locally_locally : forall (x : T) (P : T -> Prop), locally x P -> locally x (fun y => locally y P).
Proof.
intros x P [dp Hp].
exists (pos_div_2 dp).
intros y Hy.
exists (pos_div_2 dp) => /= z Hz.
apply Hp.
rewrite (double_var dp).
Admitted.

Lemma ball_le : forall (x : M) (e1 e2 : R), e1 <= e2 -> forall (y : M), ball x e1 y -> ball x e2 y.
Proof.
intros x e1 e2 H y H1.
destruct H.
assert (e2 - e1 > 0).
by apply Rgt_minus.
assert (ball y {| pos := (e2-e1); cond_pos := (H0) |} y).
apply ball_center.
replace e2 with (e1 + (e2 - e1)).
apply ball_triangle with y ; assumption.
by apply Rplus_minus.
by rewrite <- H.
