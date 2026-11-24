/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Numerical
public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.LinearSystem

import QPainleve.AlgebraicGeometry.CartierDivisor.Comparison
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.ClosedPoint
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
import QPainleve.AlgebraicGeometry.RationalPoint
import QPainleve.AlgebraicGeometry.WeilDivisor.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Dominant
import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine
import QPainleve.AlgebraicGeometry.Chow.EffectiveClass
import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import TauCeti.LinearAlgebra.QuadraticForm.LightCone

/-!
# Square-zero rational curves and rulings

On a smooth projective rational surface without exceptional curves of the first kind,
a nef effective class of square zero and canonical degree minus two has only
projective lines in its complete linear system. The canonical class detects a
component of negative canonical degree, and the surface intersection form
identifies this component with the full divisor class.

See [Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil] for the use of the
complete linear system of a square-zero curve in the classification of minimal
rational surfaces.

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Chow
open TauCeti.AlgebraicGeometry.Scheme.CartierDivisor
open LineBundleClass
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [hRat : Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => Chow.classIntersectionNumber k X
local notation "K" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "P" => LineBundleClass.primeDivisorClass
local notation "cl" => weilToLineBundleClassHom
local notation "A(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "O(" h ")" => InvertibleSheaf.dual (IsEffectiveCartier.toInvertibleSheaf h)
local notation "D(" p ")" => vanishingIdeal (Closeds.mk (closure {(p : X)}) isClosed_closure)

include hRat in
private theorem eq_of_square_zero_of_orthogonal_of_canonical_degree_eq
    {a b : LineBundleClass X} (haa : B a a = 0) (hbb : B b b = 0)
    (hab : B a b = 0) (hak : B a K = -2) (hbk : B b K = -2)
    (hapos : ∃ H : LineBundleClass X, H.IsAmple ∧ B H a ≠ 0) : a = b := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  let : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have : Module.Finite ℤ (Additive (LineBundleClass X)) := X.finite_picard_of_isRationalOver k
  obtain ⟨hQ, hsig, _⟩ := signature_realIntersectionBilinForm_of_isRationalOver k X
  obtain ⟨H, hH, hHa⟩ := hapos
  let R := realIntersectionBilinForm k X
  let v (L : LineBundleClass X) := (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul L
  have hv (L M : LineBundleClass X) : R (v L) (v M) = (B L M : ℝ) := by
    rw [realIntersectionBilinForm_tmul]
    simp
  let x := R (v H) (v a)
  let y := R (v H) (v b)
  -- This difference is orthogonal to the ample class and has square zero.
  let w := x • v b - y • v a
  have horth : R (v H) w = 0 := by
    simp [w, x, y, mul_comm]
  have hnull : R w w = 0 := by
    simp [w, LinearMap.BilinForm.sub_right, hv, haa, hbb,
      hab, Chow.classIntersectionNumber_comm b a]
  have hpos : 0 < R.toQuadraticMap (v H) := by
    rw [LinearMap.BilinMap.toQuadraticMap_apply, hv]
    exact_mod_cast classIntersectionNumber_pos_of_isAmple k hX hH hH
  have hw : w = 0 := QuadraticForm.eq_zero_of_polar_eq_zero_of_nonneg hQ hsig.le hpos
    (by rw [polar_realIntersectionBilinForm, (isSymm_realIntersectionBilinForm k X).eq, horth,
      mul_zero]) (by rw [LinearMap.BilinMap.toQuadraticMap_apply, hnull])
  have hxy : x = y := by
    have hs := congrArg (fun z ↦ R z (v K)) hw
    simp only [w, LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left,
      hv, hak, hbk, Int.cast_neg, Int.cast_ofNat, map_zero, LinearMap.zero_apply] at hs
    linarith
  have hx : x ≠ 0 := by
    dsimp only [x]
    rw [hv]
    exact_mod_cast hHa
  have he : v b = v a := by
    dsimp only [w] at hw
    rw [← hxy, ← smul_sub, smul_eq_zero, or_iff_right hx, sub_eq_zero] at hw
    exact hw
  let Q := classIntersectionBilinForm k hX
  have hp : Q.IsPerfPair := isPerfPair_classIntersectionBilinForm_of_isRationalOver k X
  refine congrArg Additive.toMul ((LinearMap.IsPerfPair.bijective_left Q).injective
    (LinearMap.ext fun z ↦ ?_))
  have hz := congrArg (R · (v z.toMul)) he.symm
  simp only [hv] at hz
  have hza := classIntersectionBilinForm_apply k hX (Additive.ofMul a) z
  have hzb := classIntersectionBilinForm_apply k hX (Additive.ofMul b) z
  exact hza.trans ((Int.cast_inj.mp hz).trans hzb.symm)

omit hRat in
private theorem exists_prime_component_of_canonical_degree_neg
    [IsIntegral X] [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hX : topologicalKrullDim X = 2) {W : SchemeWeilDivisor X} (hW : 0 ≤ W)
    (hcan : B (cl X W).toMul K < 0) :
    ∃ p ∈ W.support, B (P p) K < 0 := by
  classical
  by_contra! hn
  rw [Chow.classIntersectionNumber_comm, classIntersectionNumber_weilToLineBundleClassHom k hX K W,
    Finsupp.sum] at hcan
  exact hcan.not_ge (Finset.sum_nonneg fun p hp ↦
    mul_nonneg (hW p) (by rw [Chow.classIntersectionNumber_comm]; exact hn p hp))

include hRat in
private theorem square_eq_zero_and_canonical_degree_eq_neg_two
    [IsIntegral X] [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
    (hX : topologicalKrullDim X = 2)
    (hmin : ∀ J : X.IdealSheafData, ¬ J.IsExceptionalCurveOfFirstKind)
    (p : CodimensionOnePoint X) (hcan : B (P p) K < 0) (hsq : B (P p) (P p) ≤ 0) :
    B (P p) (P p) = 0 ∧ B (P p) K = -2 := by
  let J : X.IdealSheafData := D(p)
  have hJ : J.IsEffectiveCartier :=
    isEffectiveCartier_vanishingIdeal_closure_singleton p.property
  have : J.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k J.subschemeι
  have : J.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, QPainleve.topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
  have hclass : (LineBundleClass.mk hJ.toInvertibleSheaf)⁻¹ = P p :=
    (primeDivisorClass_def p).symm
  have hadj := J.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver k
  dsimp only at hadj
  rw [mk_toInvertibleSheaf_congr _ hJ J.ker_subschemeι, hclass] at hadj
  have hgen : J.subscheme.genus k = 0 := by omega
  have hne : B (P p) (P p) ≠ -1 := fun hz ↦ hmin J
    ((hJ.isExceptionalCurveOfFirstKind_iff_genus_eq_zero_and_classIntersectionNumber
      (k := k) hX.le).mpr ⟨hgen, by simpa only [hclass] using hz⟩)
  omega

variable {I : X.IdealSheafData}

include hRat in
/-- On a smooth projective rational surface without exceptional curves of the first kind,
every effective Cartier representative of a nef class of square zero and canonical degree
minus two is the reduced closure of a prime divisor. -/
theorem exists_eq_vanishingIdeal_of_isNef_of_self_eq_zero
    (hI : I.IsEffectiveCartier)
    (hmin : ∀ J : X.IdealSheafData, ¬ J.IsExceptionalCurveOfFirstKind)
    (hnef : (A(hI)).IsNef k (X ↘ S)) (hsq : B (A(hI)) (A(hI)) = 0)
    (hcan : B (A(hI)) K = -2) :
    ∃ p : CodimensionOnePoint X, I = D(p) := by
  classical
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  let W := hI.toCartierDivisor.toWeilDivisor
  have hW : 0 ≤ W := (isEffective_iff_toWeilDivisor_nonneg _).mp hI.isEffective_toCartierDivisor
  have hclass : (cl X W).toMul = A(hI) := by
    rw [weilToLineBundleClassHom_toWeilDivisor, toMul_ofMul, hI.toLineBundleClass_toCartierDivisor]
  obtain ⟨p, hp, hpK⟩ := exists_prime_component_of_canonical_degree_neg (k := k) hX hW (by
    rw [hclass, hcan]; decide)
  have horth := (classIntersectionNumber_weilToLineBundleClassHom_self_eq_zero_iff k hX hW
    (hclass.symm ▸ hnef)).mp (hclass.symm ▸ hclass.symm ▸ hsq) p hp
  -- Every other prime component contributes a nonnegative intersection.
  have hle : B (P p) (P p) ≤ 0 := by
    rw [Chow.classIntersectionNumber_comm, classIntersectionNumber_weilToLineBundleClassHom k hX,
      Finsupp.sum, ← Finset.sum_erase_add _ _ hp] at horth
    have hnonneg : 0 ≤ ∑ q ∈ W.support.erase p, W q * B (P p) (P q) :=
      Finset.sum_nonneg fun q hq ↦ mul_nonneg (hW q)
        (classIntersectionNumber_primeDivisorClass_nonneg_of_ne k hX
          (Finset.ne_of_mem_erase hq).symm)
    have hp' : 0 < W p := lt_of_le_of_ne (hW p) (Finsupp.mem_support_iff.mp hp).symm
    by_contra! h
    linarith [mul_pos hp' h]
  obtain ⟨hp₀, hp₂⟩ := square_eq_zero_and_canonical_degree_eq_neg_two hX hmin p hpK hle
  obtain ⟨H, hH⟩ := X.exists_isAmple_of_isProjectiveOver k
  have horth' : B (P p) (cl X W).toMul = 0 := by
    rwa [Chow.classIntersectionNumber_comm]
  have ha := eq_of_square_zero_of_orthogonal_of_canonical_degree_eq (k := k) hp₀
    (hclass.symm ▸ hclass.symm ▸ hsq) horth'
    hp₂ (hclass.symm ▸ hcan) ⟨H, hH,
      (classIntersectionNumber_primeDivisorClass_pos_of_isAmple k hX hH p).ne'⟩
  have hcoeff : 0 < W p := lt_of_le_of_ne (hW p) (Finsupp.mem_support_iff.mp hp).symm
  have hsingle := WeilDivisor.single_one_le_of_coeff_pos hW hcoeff
  have hzero : cl X (W - Finsupp.single p 1) = 0 := by
    rw [map_sub, weilToLineBundleClassHom_single, one_smul, ← primeDivisorClass_def, ha,
      ofMul_toMul, sub_self]
  have hsplit := (weilToLineBundleClassHom_eq_zero_iff_of_nonneg k hX (sub_nonneg.mpr hsingle)).mp
    hzero
  refine ⟨p, (hI.toCartierDivisor_eq_iff
    (isEffectiveCartier_vanishingIdeal_closure_singleton p.property)).mp ?_⟩
  apply toWeilDivisor_injective
  rw [toWeilDivisor_toCartierDivisor_vanishingIdeal_closure_singleton,
    ← one_smul ℤ (WeilDivisor.ofPoint p), ← WeilDivisor.single_eq_zsmul_ofPoint]
  exact sub_eq_zero.mp hsplit

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
local notation "T" => (ObjectProperty.FullSubcategory.mk (Proj.twistingSheaf 𝒜 1) inferInstance :
  InvertibleSheaf (projectiveLine k))

include hRat in
/-- A nef effective Cartier divisor of square zero and canonical degree minus two on a
smooth projective rational surface without exceptional curves of the first kind is a
projective line over the base field. -/
theorem exists_iso_projectiveLine_of_isNef_of_self_eq_zero
    (hI : I.IsEffectiveCartier) (hmin : ∀ J : X.IdealSheafData, ¬ J.IsExceptionalCurveOfFirstKind)
    (hnef : (A(hI)).IsNef k (X ↘ S)) (hsq : B (A(hI)) (A(hI)) = 0)
    (hcan : B (A(hI)) K = -2) :
    ∃ e : I.subscheme ≅ projectiveLine k, e.hom.IsOver S := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  obtain ⟨p, hp⟩ := hI.exists_eq_vanishingIdeal_of_isNef_of_self_eq_zero hmin hnef hsq hcan
  have : IsIntegral I.subscheme := hp ▸ isIntegral_subscheme_vanishingIdeal_closure_singleton p.val
  have : I.subscheme.IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k I.subschemeι
  have : I.subscheme.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨inferInstance, inferInstance, hp ▸ topologicalKrullDim_vanishingIdeal_subscheme k hX p⟩
  have hg := I.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver k
  dsimp only at hg
  rw [mk_toInvertibleSheaf_congr _ hI I.ker_subschemeι, hsq, hcan] at hg
  exact genus_eq_zero_iff_exists_iso_projectiveLine.mp (by omega)

omit [X.Over S] [IsAlgClosed k] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ S)] hRat in
private theorem isDominant_of_pullback_twistingSheaf_ne_one [IsIntegral X]
    (f : X ⟶ projectiveLine k) (h : pullback f (LineBundleClass.mk T) ≠ 1) : IsDominant f := by
  rw [isDominant_iff_genericPoint_eq]
  by_contra hn
  let p := f (genericPoint X)
  have hdim := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := projectiveLine k) k
  have hp : IsClosed ({p} : Set (projectiveLine k)) :=
    TauCeti.AlgebraicGeometry.Scheme.isClosed_singleton_of_ne_genericPoint hdim.le hn
  let j := (projectiveLine k).fromSpecResidueField p
  have : IsClosedImmersion j := isClosed_singleton_iff_isClosedImmersion.mp hp
  have hrange : Set.range f ⊆ {p} := by
    rintro _ ⟨x, rfl⟩
    exact ((genericPoint_specializes x).map f.continuous).mem_closed hp (Set.mem_singleton p)
  have hker : j.ker ≤ f.ker := by
    rw [Scheme.ker_fromSpecResidueField_eq_vanishingIdeal]
    apply vanishingIdeal_le_ker_of_range_subset f
    rw [Closeds.coe_mk, hp.closure_eq]
    exact hrange
  let g := IsClosedImmersion.lift j f hker
  have hg : g ≫ j = f := IsClosedImmersion.lift_fac _ _ _
  exact h (by rw [← hg, ← pullback_comp,
    Subsingleton.elim (pullback j (LineBundleClass.mk T)) 1, pullback_one])

include hRat in
private theorem exists_projectiveLine_fiber_of_pullback_twistingSheaf
    [IsIntegral X] (f : X ⟶ projectiveLine k) [IsDominant f]
    (hmin : ∀ J : X.IdealSheafData, ¬ J.IsExceptionalCurveOfFirstKind)
    (hnef : (pullback f (LineBundleClass.mk T)).IsNef k (X ↘ S))
    (hsq : B (pullback f (LineBundleClass.mk T)) (pullback f (LineBundleClass.mk T)) = 0)
    (hcan : B (pullback f (LineBundleClass.mk T)) K = -2)
    (p : projectiveLine k) (hp : IsClosed ({p} : Set (projectiveLine k))) :
    ∃ e : f.fiber p ≅ projectiveLine k,
      e.hom ≫ (projectiveLine k ↘ S) = f.fiberι p ≫ X ↘ S := by
  let j := (projectiveLine k).fromSpecResidueField p
  have : IsClosedImmersion j := isClosed_singleton_iff_isClosedImmersion.mp hp
  have : TauCeti.AlgebraicGeometry.IsRegular (projectiveLine k) :=
    ⟨fun _ ↦ inferInstance⟩
  have hP := (projectiveLine k).isEffectiveCartier_ker_fromSpecResidueField_of_dim_eq_one hp
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)
  have ht : A(hP) = LineBundleClass.mk T := by
    refine congrArg Additive.toMul ((projectiveLine.picardDegreeEquiv k).injective
      (show projectiveLine.picardDegreeEquiv k (Additive.ofMul (A(hP))) =
        projectiveLine.picardDegreeEquiv k (Additive.ofMul (LineBundleClass.mk T)) from ?_))
    rw [projectiveLine.picardDegreeEquiv_apply, projectiveLine.picardDegreeEquiv_apply,
      toMul_ofMul, toMul_ofMul, projectiveLine.eulerDegree_inv,
      eulerDegree_mk_ker_fromSpecResidueField hp,
      (projectiveLine k ↘ S).residueDegree_eq_one_of_isClosed hp, Nat.cast_one, neg_neg,
      eulerDegree_mk, projectiveLine.eulerDegree_twistingSheaf]
  let J := j.ker.comap f
  have hJ : J.IsEffectiveCartier := hP.comap_of_isDominant f
  have ha : A(hJ) = pullback f (LineBundleClass.mk T) := by
    rw [← ht, pullback_inv, hP.pullback_mk_toInvertibleSheaf hJ]
  obtain ⟨e, he⟩ := hJ.exists_iso_projectiveLine_of_isNef_of_self_eq_zero
    hmin (ha ▸ hnef) (ha ▸ ha ▸ hsq) (ha ▸ hcan)
  have hker : (f.fiberι p).ker = J := IdealSheafData.ker_fst_of_isClosedImmersion j f
  have : IsClosedImmersion (f.fiberι p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f j).flip inferInstance
  let a := asIso (f.fiberι p).toImage ≪≫ eqToIso (congrArg IdealSheafData.subscheme hker)
  have ha' : a.hom ≫ J.subschemeι = f.fiberι p := by
    rw [Iso.trans_hom, asIso_hom, eqToIso.hom, Category.assoc,
      ← eqToHom_naturality IdealSheafData.subschemeι hker]
    simp
  have : e.hom.IsOver S := he
  refine ⟨a ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Category.assoc, comp_over e.hom S, IdealSheafData.over_eq_subschemeι_comp,
    ← Category.assoc, ha']

attribute [local instance] MvPolynomial.gradedAlgebra

omit [IsAlgClosed k] [X.IsProjectiveOver k] [SmoothOfRelativeDimension 2 (X ↘ S)] hRat in
private theorem exists_to_projectiveLine_of_basis (L : InvertibleSheaf X)
    (v : Module.Basis (ULift.{u} (Fin 2)) k Γ(L.obj, ⊤)) (hglob : L.IsGloballyGenerated) :
    ∃ f : X ⟶ projectiveLine k, f.IsOver S ∧
      pullback f (LineBundleClass.mk T) = LineBundleClass.mk L := by
  let b := (Pi.basisFun k (Fin 2)).reindex Equiv.ulift.symm
  let hcover := hglob.iSup_nonvanishingLocus_basis_eq_top v
  let g := L.obj.toProjectiveSpace (X ↘ S) v hcover
  let f := g ≫ b.polynomialProjIso.hom
  have hbase : b.polynomialProjIso.hom ≫ (projectiveLine k ↘ S) =
      Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 2)) k) :=
    b.polynomialProjIso_hom_over
  have hf : f ≫ (projectiveLine k ↘ S) = X ↘ S := by
    rw [Category.assoc, hbase,
      L.obj.toProjectiveSpace_toSpecCoeff (X ↘ S) v hcover]
  obtain ⟨a, -⟩ := L.obj.exists_iso_pullbackTwistingSheaf_toProjectiveSpace (X ↘ S) v hcover
  refine ⟨f, ⟨hf⟩, ?_⟩
  dsimp only [f]
  rw [← pullback_comp, pullback_mk, pullback_mk]
  exact mk_eq_mk_iff.mpr ⟨
    (Scheme.Modules.pullback g).mapIso (b.polynomialProjIsoPullbackTwistingSheafIso 1) ≪≫ a⟩

include hRat in
/-- The complete pencil of an integral genus-zero Cartier divisor of square zero defines a
morphism to the projective line whose pullback of `𝒪(1)` is the divisor class. -/
theorem exists_to_projectiveLine_of_square_zero_rational_curve
    (hI : I.IsEffectiveCartier) [I.subscheme.IsCurveOver k]
    (hsq : B (A(hI)) (A(hI)) = 0) (hg : I.subscheme.genus k = 0) :
    ∃ f : X ⟶ projectiveLine k, f.IsOver S ∧ pullback f (LineBundleClass.mk T) = A(hI) := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hC := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := I.subscheme) k
  obtain ⟨e, he⟩ := genus_eq_zero_iff_exists_iso_projectiveLine.mp hg
  have : e.hom.IsOver S := he
  have : e.symm.hom.IsOver S := by
    refine ⟨?_⟩
    rw [Iso.symm_hom, ← comp_over e.hom S, e.inv_hom_id_assoc]
  let L := O(hI)
  have hL : LineBundleClass.mk L = A(hI) := by rw [← inv_mk]
  have hdeg : intersectionNumber k (e.inv ≫ I.subschemeι) (LineBundleClass.mk L) = 0 := by
    rw [← intersectionNumber_pullback, LineBundleClass.intersectionNumber_def,
      eulerDegree_pullback_of_isIso e.inv (comp_over e.inv S),
      ← LineBundleClass.intersectionNumber_def,
      ← classIntersectionNumber_eq_intersectionNumber_subschemeι k hX.le hI hC, hL, hsq]
  obtain ⟨hglob, hdim⟩ :=
    hI.isGloballyGenerated_and_finrank_globalSections_dual_of_projectiveLine e.symm
      (X.subsingleton_cohomology_trivial_of_isRationalOver k (i := 1) Nat.one_pos) (d := 0) hdeg
  have hdim : Module.finrank k Γ(L.obj, ⊤) = 2 := hdim
  have : Module.Finite k Γ(L.obj, ⊤) := Module.finite_of_finrank_pos (hdim.symm ▸ by decide)
  let v := (Module.finBasisOfFinrankEq k Γ(L.obj, ⊤) hdim).reindex Equiv.ulift.symm
  obtain ⟨f, hf, hclass⟩ := exists_to_projectiveLine_of_basis L v hglob
  exact ⟨f, hf, hclass.trans hL⟩

include hRat in
/-- The complete linear system of a square-zero integral genus-zero curve on a smooth
projective rational surface without exceptional curves of the first kind gives a proper, flat,
surjective morphism to the projective line. Every closed fiber is isomorphic over the base
field to the projective line, with its scheme-theoretic fiber structure. -/
theorem exists_ruling_of_square_zero_rational_curve
    (hI : I.IsEffectiveCartier) [I.subscheme.IsCurveOver k]
    (hmin : ∀ J : X.IdealSheafData, ¬ J.IsExceptionalCurveOfFirstKind)
    (hsq : B (A(hI)) (A(hI)) = 0) (hg : I.subscheme.genus k = 0) :
    ∃ f : X ⟶ projectiveLine k, f.IsOver S ∧ IsProper f ∧ Flat f ∧ Surjective f ∧
      pullback f (LineBundleClass.mk T) = A(hI) ∧
      ∀ p : projectiveLine k, IsClosed ({p} : Set (projectiveLine k)) →
        ∃ e : f.fiber p ≅ projectiveLine k,
          e.hom ≫ (projectiveLine k ↘ S) = f.fiberι p ≫ X ↘ S := by
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsIntegral X := hRat.isIntegral_of_smooth
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  have : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hX := topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ S) (n := 2)
  have hC := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := I.subscheme) k
  have hc := I.subschemeι.two_mul_genus_sub_two_eq_intersection_of_isRationalOver k
  dsimp only at hc
  rw [mk_toInvertibleSheaf_congr _ hI I.ker_subschemeι, hsq, hg, Nat.cast_zero] at hc
  have hcan : B (A(hI)) K = -2 := by omega
  have hnef : (A(hI)).IsNef k (X ↘ S) := by
    let p : CodimensionOnePoint X := ⟨I.subschemeι (genericPoint I.subscheme),
      I.subschemeι.coheight_apply_genericPoint_eq_one_of_dim_eq_two k hX hC⟩
    have hp : I = D(p) := I.ker_subschemeι.symm.trans
      I.subschemeι.ker_eq_vanishingIdeal_closure_genericPoint
    have ha : A(hI) = P p := by
      rw [primeDivisorClass_def, mk_toInvertibleSheaf_congr hI _ hp]
    rw [isNef_iff_classIntersectionNumber_nonneg k hX, ha]
    intro q
    rcases eq_or_ne p q with rfl | hn
    · rw [← ha, hsq]
    · exact classIntersectionNumber_primeDivisorClass_nonneg_of_ne k hX hn
  obtain ⟨f, hf, hcl⟩ := hI.exists_to_projectiveLine_of_square_zero_rational_curve hsq hg
  have : f.IsOver S := hf
  have : IsProper (f ≫ (projectiveLine k ↘ S)) := (comp_over f S).symm ▸
    (inferInstance : IsProper (X ↘ S))
  have hproper : IsProper f := .of_comp f (projectiveLine k ↘ S)
  have : IsDominant f := isDominant_of_pullback_twistingSheaf_ne_one f (by
    rw [hcl]
    intro hh
    rw [hh, classIntersectionNumber_one_left] at hcan
    omega)
  have : RelativeDimensionLE 1 (projectiveLine k ↘ S) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have : Smooth (projectiveLine k ↘ S) := SmoothOfRelativeDimension.smooth 1 _
  have hflat : Flat f := f.flat_of_isDominant_of_smooth (projectiveLine k ↘ S)
  have hsurj : Surjective f := surjective_of_isDominant_of_isClosed_range f
    (by simpa only [Set.image_univ] using f.isClosedMap _ isClosed_univ)
  exact ⟨f, hf, hproper, hflat, hsurj, hcl,
    exists_projectiveLine_fiber_of_pullback_twistingSheaf f hmin
      (hcl ▸ hnef) (hcl ▸ hcl ▸ hsq) (hcl ▸ hcan)⟩

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
