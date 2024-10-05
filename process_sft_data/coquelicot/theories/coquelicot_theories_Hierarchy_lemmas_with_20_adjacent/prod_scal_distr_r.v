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

Lemma filterlim_scal_r (k : K) (x : V) : filterlim (fun z : V => scal k z) (locally x) (locally (scal k x)).
Proof.
eapply filterlim_comp_2.
by apply filterlim_const.
by apply filterlim_id.
Admitted.

Lemma filterlim_scal_l (k : K) (x : V) : filterlim (fun z => scal z x) (locally k) (locally (scal k x)).
Proof.
eapply filterlim_comp_2.
by apply filterlim_id.
by apply filterlim_const.
Admitted.

Lemma filterlim_opp : forall x : V, filterlim opp (locally x) (locally (opp x)).
Proof.
intros x.
rewrite -scal_opp_one.
apply filterlim_ext with (2 := filterlim_scal_r _ _).
Admitted.

Lemma filterlim_mult {K : AbsRing} (x y : K) : filterlim (fun z => mult (fst z) (snd z)) (filter_prod (locally x) (locally y)) (locally (mult x y)).
Proof.
Admitted.

Lemma filterlim_locally_ball_norm : forall {K : AbsRing} {T} {U : NormedModule K} {F : (T -> Prop) -> Prop} {FF : Filter F} (f : T -> U) (y : U), filterlim f F (locally y) <-> forall eps : posreal, F (fun x => ball_norm y eps (f x)).
Proof.
intros K T U F FF f y.
split.
-
intros Cf eps.
apply (Cf (fun x => ball_norm y eps x)).
apply locally_le_locally_norm.
apply locally_norm_ball_norm.
-
intros Cf.
apply (filterlim_filter_le_2 _ (locally_norm_le_locally y)).
intros P [eps He].
apply: filter_imp (Cf eps).
intros t.
Admitted.

Lemma iota_unique : forall (P : V -> Prop) (x : V), (forall y, P y -> y = x) -> P x -> iota P = x.
Proof.
intros P x HP Px.
apply eq_close.
intros eps.
apply: iota_correct_weak Px eps.
intros x' y Px' Py eps.
rewrite (HP _ Py) -(HP _ Px').
Admitted.

Lemma iota_correct : forall P : V -> Prop, (exists! x : V, P x) -> P (iota P).
Proof.
intros P [x [Px HP]].
rewrite (iota_unique _ x) ; try exact Px.
intros y Py.
Admitted.

Lemma iota_is_filter_lim {F} {FF : ProperFilter' F} (l : V) : is_filter_lim F l -> iota (is_filter_lim F) = l.
Proof.
intros Hl.
apply: iota_unique (Hl) => l' Hl'.
Admitted.

Lemma iota_filterlim_locally {F} {FF : ProperFilter' F} (f : T -> V) l : filterlim f F (locally l) -> iota (fun x => filterlim f F (locally x)) = l.
Proof.
Admitted.

Lemma iota_filterlimi_locally {F} {FF : ProperFilter' F} (f : T -> V -> Prop) l : F (fun x => forall y1 y2, f x y1 -> f x y2 -> y1 = y2) -> filterlimi f F (locally l) -> iota (fun x => filterlimi f F (locally x)) = l.
Proof.
intros Hf Hl.
apply: iota_unique (Hl) => l' Hl'.
Admitted.

Lemma prod_plus_comm : forall x y : U * V, prod_plus x y = prod_plus y x.
Proof.
intros x y.
Admitted.

Lemma prod_plus_assoc : forall x y z : U * V, prod_plus x (prod_plus y z) = prod_plus (prod_plus x y) z.
Proof.
intros x y z.
Admitted.

Lemma prod_plus_zero_r : forall x : U * V, prod_plus x prod_zero = x.
Proof.
intros [u v].
Admitted.

Lemma prod_plus_opp_r : forall x : U * V, prod_plus x (prod_opp x) = prod_zero.
Proof.
intros x.
Admitted.

Lemma prod_ball_center : forall (x : U * V) (eps : posreal), prod_ball x eps x.
Proof.
intros x eps.
Admitted.

Lemma prod_ball_sym : forall (x y : U * V) (eps : R), prod_ball x eps y -> prod_ball y eps x.
Proof.
intros x y eps [H1 H2].
Admitted.

Lemma prod_ball_triangle : forall (x y z : U * V) (e1 e2 : R), prod_ball x e1 y -> prod_ball y e2 z -> prod_ball x (e1 + e2) z.
Proof.
intros x y z e1 e2 [H1 H2] [H3 H4].
Admitted.

Lemma prod_scal_assoc : forall (x y : K) (u : U * V), prod_scal x (prod_scal y u) = prod_scal (mult x y) u.
Proof.
intros x y u.
Admitted.

Lemma prod_scal_one : forall u : U * V, prod_scal one u = u.
Proof.
intros [u v].
Admitted.

Lemma prod_scal_distr_l : forall (x : K) (u v : U * V), prod_scal x (prod_plus u v) = prod_plus (prod_scal x u) (prod_scal x v).
Proof.
intros x u v.
Admitted.

Lemma sqrt_plus_sqr : forall x y : R, Rmax (Rabs x) (Rabs y) <= sqrt (x ^ 2 + y ^ 2) <= sqrt 2 * Rmax (Rabs x) (Rabs y).
Proof.
intros x y.
split.
-
rewrite -!sqrt_Rsqr_abs.
apply Rmax_case ; apply sqrt_le_1_alt, Rminus_le_0 ; rewrite /Rsqr /= ; ring_simplify ; by apply pow2_ge_0.
-
Admitted.

Lemma prod_norm_triangle : forall x y : U * V, prod_norm (plus x y) <= prod_norm x + prod_norm y.
Proof.
intros [xu xv] [yu yv].
rewrite /prod_norm /= !Rmult_1_r.
apply Rle_trans with (sqrt (Rsqr (norm xu + norm yu) + Rsqr (norm xv + norm yv))).
-
apply sqrt_le_1_alt.
apply Rplus_le_compat.
apply Rsqr_le_abs_1.
rewrite -> 2!Rabs_pos_eq.
apply: norm_triangle.
apply Rplus_le_le_0_compat ; apply norm_ge_0.
apply norm_ge_0.
apply Rsqr_le_abs_1.
rewrite -> 2!Rabs_pos_eq.
apply: norm_triangle.
apply Rplus_le_le_0_compat ; apply norm_ge_0.
apply norm_ge_0.
-
apply Rsqr_incr_0_var.
apply Rminus_le_0.
unfold Rsqr ; simpl ; ring_simplify.
rewrite /pow ?Rmult_1_r.
rewrite ?sqrt_sqrt ; ring_simplify.
replace (-2 * norm xu * norm yu - 2 * norm xv * norm yv) with (-(2 * (norm xu * norm yu + norm xv * norm yv))) by ring.
rewrite Rmult_assoc -sqrt_mult.
rewrite Rplus_comm.
apply -> Rminus_le_0.
apply Rmult_le_compat_l.
apply Rlt_le, Rlt_0_2.
apply Rsqr_incr_0_var.
apply Rminus_le_0.
rewrite /Rsqr ?sqrt_sqrt ; ring_simplify.
replace (norm xu ^ 2 * norm yv ^ 2 - 2 * norm xu * norm xv * norm yu * norm yv + norm xv ^ 2 * norm yu ^ 2) with ((norm xu * norm yv - norm xv * norm yu) ^ 2) by ring.
apply pow2_ge_0.
repeat apply Rplus_le_le_0_compat ; apply Rmult_le_pos ; apply pow2_ge_0.
apply sqrt_pos.
apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
replace (norm xu ^ 2 + 2 * norm xu * norm yu + norm yu ^ 2 + norm xv ^ 2 + 2 * norm xv * norm yv + norm yv ^ 2) with ((norm xu + norm yu) ^ 2 + (norm xv + norm yv) ^ 2) by ring.
apply Rplus_le_le_0_compat ; apply pow2_ge_0.
apply Rplus_le_le_0_compat ; apply pow2_ge_0.
apply Rplus_le_le_0_compat ; apply pow2_ge_0.
Admitted.

Lemma prod_norm_scal : forall (l : K) (x : U * V), prod_norm (scal l x) <= abs l * prod_norm x.
Proof.
intros l [xu xv].
rewrite /prod_norm /= -(sqrt_Rsqr (abs l)).
2: apply abs_ge_0.
rewrite !Rmult_1_r.
rewrite -sqrt_mult.
2: apply Rle_0_sqr.
apply sqrt_le_1_alt.
rewrite Rmult_plus_distr_l.
unfold Rsqr.
apply Rplus_le_compat.
replace (abs l * abs l * (norm xu * norm xu)) with ((abs l * norm xu) * (abs l * norm xu)) by ring.
apply Rmult_le_compat.
apply norm_ge_0.
apply norm_ge_0.
exact (norm_scal l xu).
exact (norm_scal l xu).
replace (abs l * abs l * (norm xv * norm xv)) with ((abs l * norm xv) * (abs l * norm xv)) by ring.
apply Rmult_le_compat.
apply norm_ge_0.
apply norm_ge_0.
exact (norm_scal l xv).
exact (norm_scal l xv).
Admitted.

Lemma prod_norm_compat1 : forall (x y : U * V) (eps : R), prod_norm (minus y x) < eps -> ball x eps y.
Proof.
intros [xu xv] [yu yv] eps H.
generalize (Rle_lt_trans _ _ _ (proj1 (sqrt_plus_sqr _ _)) H).
rewrite -> !Rabs_pos_eq by apply norm_ge_0.
intros H'.
split ; apply norm_compat1 ; apply Rle_lt_trans with (2 := H').
apply Rmax_l.
Admitted.

Lemma prod_norm_compat2 : forall (x y : U * V) (eps : posreal), ball x eps y -> prod_norm (minus y x) < prod_norm_factor * eps.
Proof.
intros [xu xv] [yu yv] eps [Bu Bv].
apply Rle_lt_trans with (1 := proj2 (sqrt_plus_sqr _ _)).
simpl.
rewrite Rmult_assoc.
apply Rmult_lt_compat_l.
apply sqrt_lt_R0.
apply Rlt_0_2.
rewrite -> !Rabs_pos_eq by apply norm_ge_0.
rewrite Rmax_mult.
apply Rmax_case.
apply Rlt_le_trans with (2 := Rmax_l _ _).
now apply norm_compat2.
apply Rlt_le_trans with (2 := Rmax_r _ _).
now apply norm_compat2.
apply Rlt_le.
Admitted.

Lemma prod_norm_eq_zero : forall x : U * V, prod_norm x = 0 -> x = zero.
Proof.
intros [xu xv] H.
apply sqrt_eq_0 in H.
rewrite !(pow_Rsqr _ 1) !pow_1 in H.
apply Rplus_sqr_eq_0 in H.
destruct H as [H1 H2].
apply norm_eq_zero in H1.
apply norm_eq_zero in H2.
simpl in H1, H2.
now rewrite H1 H2.
Admitted.

Lemma norm_prod {K : AbsRing} {U : NormedModule K} {V : NormedModule K} (x : U) (y : V) : Rmax (norm x) (norm y) <= norm (x,y) <= sqrt 2 * Rmax (norm x) (norm y).
Proof.
rewrite -(Rabs_pos_eq (norm x)).
rewrite -(Rabs_pos_eq (norm y)).
apply sqrt_plus_sqr.
by apply norm_ge_0.
Admitted.

Lemma mk_Tn_bij {T} {n : nat} (x0 : T) (v : Tn n T) : mk_Tn n (coeff_Tn x0 v) = v.
Proof.
induction n ; simpl.
now apply unit_ind.
Admitted.

Lemma coeff_Tn_bij {T} {n : nat} (x0 : T) (u : nat -> T) : forall i, (i < n)%nat -> coeff_Tn x0 (mk_Tn n u) i = u i.
Proof.
revert u ; induction n => /= u i Hi.
by apply lt_n_O in Hi.
destruct i.
by [].
Admitted.

Lemma coeff_Tn_ext {T} {n : nat} (x1 x2 : T) (v1 v2 : Tn n T) : v1 = v2 <-> forall i, (i < n)%nat -> coeff_Tn x1 v1 i = coeff_Tn x2 v2 i.
Proof.
split.
+
move => -> {v1}.
induction n => i Hi.
by apply lt_n_O in Hi.
destruct i ; simpl.
by [].
by apply IHn, lt_S_n.
+
induction n => H.
apply unit_ind ; move: (v1) ; now apply unit_ind.
apply injective_projections.
by apply (H O), lt_O_Sn.
apply IHn => i Hi.
Admitted.

Lemma mk_Tn_ext {T} (n : nat) (u1 u2 : nat -> T) : (forall i, (i < n)%nat -> (u1 i) = (u2 i)) <-> (mk_Tn n u1) = (mk_Tn n u2).
Proof.
move: u1 u2 ; induction n ; simpl ; split ; intros.
by [].
by apply lt_n_O in H0.
apply f_equal2.
by apply H, lt_O_Sn.
apply IHn => i Hi.
by apply H, lt_n_S.
destruct i.
by apply (f_equal (@fst _ _)) in H.
move: i {H0} (lt_S_n _ _ H0).
apply IHn.
Admitted.

Lemma mk_matrix_bij {m n : nat} (x0 : T) (A : matrix m n) : mk_matrix m n (coeff_mat x0 A) = A.
Proof.
unfold mk_matrix, coeff_mat.
unfold matrix in A.
rewrite -{2}(mk_Tn_bij (mk_Tn _ (fun _ => x0)) A).
apply mk_Tn_ext.
intros i Hi.
Admitted.

Lemma coeff_mat_bij {m n : nat} (x0 : T) (u : nat -> nat -> T) : forall i j, (i < m)%nat -> (j < n)%nat -> coeff_mat x0 (mk_matrix m n u) i j = u i j.
Proof.
intros i j Hi Hj.
unfold mk_matrix, coeff_mat.
Admitted.

Lemma coeff_mat_ext_aux {m n : nat} (x1 x2 : T) (v1 v2 : matrix m n) : v1 = v2 <-> forall i j, (i < m)%nat -> (j < n)%nat -> (coeff_mat x1 v1 i j) = (coeff_mat x2 v2 i j).
Proof.
split => Hv.
+
move => i j Hi Hj.
by repeat apply coeff_Tn_ext.
+
unfold matrix in v1, v2.
rewrite -(mk_matrix_bij x1 v1) -(mk_matrix_bij x2 v2).
unfold mk_matrix.
apply mk_Tn_ext => i Hi.
apply mk_Tn_ext => j Hj.
Admitted.

Lemma coeff_mat_ext {m n : nat} (x0 : T) (v1 v2 : matrix m n) : v1 = v2 <-> forall i j, (coeff_mat x0 v1 i j) = (coeff_mat x0 v2 i j).
Proof.
split.
by move => ->.
intro H.
Admitted.

Lemma mk_matrix_ext (m n : nat) (u1 u2 : nat -> nat -> T) : (forall i j, (i < m)%nat -> (j < n)%nat -> (u1 i j) = (u2 i j)) <-> (mk_matrix m n u1) = (mk_matrix m n u2).
Proof.
split => H.
+
apply (mk_Tn_ext m) => i Hi.
apply (mk_Tn_ext n) => j Hj.
by apply H.
+
intros i j Hi Hj.
apply (mk_Tn_ext n).
apply (mk_Tn_ext m (fun i => mk_Tn n (u1 i)) (fun i => mk_Tn n (u2 i))).
apply H.
by [].
Admitted.

Lemma Mplus_comm : forall A B : @matrix G m n, Mplus A B = Mplus B A.
Proof.
intros A B.
apply mk_matrix_ext => i j Hi Hj.
Admitted.

Lemma Mplus_assoc : forall A B C : @matrix G m n, Mplus A (Mplus B C) = Mplus (Mplus A B) C.
Proof.
intros A B C.
apply mk_matrix_ext => /= i j Hi Hj.
rewrite ?coeff_mat_bij => //.
Admitted.

Lemma Mplus_zero_r : forall A : @matrix G m n, Mplus A Mzero = A.
Proof.
intros A.
apply (coeff_mat_ext_aux zero zero) => i j Hi Hj.
rewrite ?coeff_mat_bij => //=.
Admitted.

Lemma Mplus_opp_r : forall A : @matrix G m n, Mplus A (Mopp A) = Mzero.
Proof.
intros A.
apply (coeff_mat_ext_aux zero zero) => i j Hi Hj.
rewrite ?coeff_mat_bij => //=.
Admitted.

Lemma prod_scal_distr_r : forall (x y : K) (u : U * V), prod_scal (plus x y) u = prod_plus (prod_scal x u) (prod_scal y u).
Proof.
intros x y u.
apply (f_equal2 pair) ; apply scal_distr_r.
