/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Numerical
public import QPainleve.AlgebraicGeometry.CartierDivisor.Excision
public import TauCeti.LinearAlgebra.BilinearForm.Prod
import QPainleve.AlgebraicGeometry.Blowup.Point.Fiber
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Picard markings for specified contractions

Suppose two ordered point-blowup towers identify their final surfaces. In the Picard
coordinates of the second tower, the Picard group of the first base is the orthogonal
complement of the span of the first tower's total exceptional classes. The inverse
of this marking is pullback to the common surface in the second tower's coordinates.

This applies to a nodal contraction of an ordered toric blowup model. The product
pairing and the use of total exceptional classes follow the point-blowup formula in
[Hacking, *Compact Complex Surfaces*, Proposition 7.1][Hacking].

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=34
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry
open LineBundleClass LinearMap.BilinForm

universe u

namespace QPainleve.BlowupTower

variable {X Y Z W : Scheme.{u}} {m n : ℕ}
  {T : BlowupTower X m Y} {U : BlowupTower Z n W}

local notation "Pic(" S ")" => Additive (LineBundleClass S)
local notation "f(" k "," S ")" => (S ↘ Spec (CommRingCat.of k))

section ExceptionalRestriction

variable {k : Type u} [Field k] [PerfectField k] [IsNoetherian X]
  {A : Scheme.{u}}

/-- Each total exceptional class restricts trivially to the preimage of the
isomorphism locus of a closed-point blowup tower. -/
theorem IsClosedPointTower.pullback_exceptionalClass_eq_one_of_mapsTo_isoLocus
    (hT : IsClosedPointTower X T) (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    (g : A ⟶ Y) (hg : ∀ a, T.toBase (g a) ∈ T.toBase.isoLocus) (j : Fin m) :
    pullback g (T.exceptionalClass j) = 1 := by
  induction hT with
  | nil => exact j.elim0
  | @snoc d V S I hS p hp hI ih =>
    let fV := S.toBase ≫ f
    have : SmoothOfRelativeDimension 2 fV := hS.smoothOfRelativeDimension f
    have : IsLocallyNoetherian V := S.isNoetherian.toIsLocallyNoetherian
    have : IsProper S.toBase := S.isProper_toBase
    have : Smooth fV := SmoothOfRelativeDimension.smooth 2 fV
    have : IsRegular V := IsRegular.of_smooth fV
    have : IsRegularLocalRing (V.presheaf.stalk p) := isRegularLocalRing_stalk_of_smooth fV p
    have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq fV 2).mp
      inferInstance).2 p hp
    rw [V.ker_fromSpecResidueField_eq_vanishingIdeal] at hI
    subst I
    let J := Scheme.IdealSheafData.vanishingIdeal ⟨closure {p}, isClosed_closure⟩
    have : Surjective J.blowupToBase :=
      Scheme.IdealSheafData.surjective_blowupToBase_point hp hdim
    have hc : J.blowupToBase.centre = {p} :=
      Scheme.IdealSheafData.centre_blowupToBase_closed_point hp hdim
    have hcomp := J.blowupToBase.centre_comp S.toBase
    rw [hc] at hcomp
    have hmiss (a : A) :
        S.toBase (J.blowupToBase (g a)) ∉ S.toBase.centre ∪ S.toBase '' {p} := by
      rw [← hcomp, Scheme.Hom.centre_def,
        Set.mem_compl_iff, not_not]
      simpa only [toBase_snoc, Scheme.Hom.comp_apply, J, SetLike.mem_coe] using hg a
    refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · rw [exceptionalClass_snoc_last, ← J.blowupExceptionalClass_def]
      apply J.pullback_blowupExceptionalClass_eq_one
      rw [J.comap_eq_top_iff, ← top_le_iff]
      intro a _
      apply (g ≫ J.blowupToBase).mem_preimage.mpr
      have hs : (J.support : Set V) = {p} :=
        (Scheme.IdealSheafData.coe_support_vanishingIdeal _).trans hp.closure_eq
      rw [← SetLike.mem_coe, Closeds.coe_compl, hs, Set.mem_compl_iff, Scheme.Hom.comp_apply]
      exact fun ha ↦ hmiss a (Or.inr ⟨_, ha, rfl⟩)
    · rw [exceptionalClass_snoc_castSucc, pullback_comp]
      refine ih (g ≫ J.blowupToBase) (fun a ↦ ?_) l
      rw [Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← S.toBase.compl_centre]
      exact fun ha ↦ hmiss a (Or.inl ha)

end ExceptionalRestriction

section ExceptionalSpan

variable (k : Type u) [Field k] [PerfectField k] [Z.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (f(k,Z))] [IsIntegral Z] [IsNoetherian Z]

/-- The span of the total exceptional classes of `T`, expressed in the marking of `U`
via the specified isomorphism of the final schemes. -/
def markedExceptionalSpan (hU : IsClosedPointTower Z U) (T : BlowupTower X m Y) (e : W ≅ Y) :
    Submodule ℤ (Pic(Z) × (Fin n → ℤ)) :=
  Submodule.span ℤ (Set.range fun j ↦
    (U.picardMarking hU (f(k,Z))).symm (Additive.ofMul (pullback e.hom (T.exceptionalClass j))))

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (f(k,X))]
  [IsIntegral X] [IsNoetherian X]
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y)

local notation "E" => picardEquivOfCommonResolution k hT hU e
local notation "P" => markedExceptionalSpan k hU T e

/-- The total exceptional span is generated by the images of the exceptional coordinate
vectors in the common-resolution equivalence. -/
theorem markedExceptionalSpan_eq_span_range :
    P = Submodule.span ℤ (Set.range fun j ↦ E (0, Pi.single j 1)) := by
  unfold markedExceptionalSpan
  congr 2
  funext j
  apply (U.picardMarking hU (f(k,Z))).injective
  rw [LinearEquiv.apply_symm_apply, picardMarking_apply, picardHom_picardEquivOfCommonResolution,
    picardHom_apply_single T j 1, zpow_one]

/-- The span of the exceptional classes is the pure exceptional summand in the
coordinates of the contraction tower. -/
theorem mem_markedExceptionalSpan_iff (a : Pic(Z) × (Fin n → ℤ)) :
    a ∈ P ↔ ((E).symm a).1 = 0 := by
  let L := (E).toLinearMap.comp (LinearMap.inr ℤ (Pic(X)) (Fin m → ℤ))
  have hspan : P = L.range := by
    rw [markedExceptionalSpan_eq_span_range k hT hU e, ← Submodule.map_top,
      ← (Pi.basisFun ℤ (Fin m)).span_eq, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp only [Function.comp_apply, Pi.basisFun_apply, L, LinearMap.comp_apply,
      LinearMap.inr_apply, LinearEquiv.coe_coe]
  rw [hspan, LinearMap.mem_range]
  constructor
  · rintro ⟨b, rfl⟩
    simp [L]
  · intro h
    refine ⟨((E).symm a).2, ?_⟩
    have ha : (0, ((E).symm a).2) = (E).symm a := Prod.ext h.symm rfl
    simpa only [L, LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe, ha]
      using (E).apply_symm_apply a

include hT in
/-- The total exceptional span in the ordered marking is the span of the actual
prime divisors contracted by the projection, expressed in that same marking. -/
theorem markedExceptionalSpan_eq_comap_primeDivisorSpanCompl :
    let p := e.hom ≫ T.toBase
    let : IsNoetherian W := U.isNoetherian
    let : IsIntegral W := hU.isIntegral (f(k,Z))
    let := hU.smoothOfRelativeDimension (f(k,Z))
    let := (U.toBase ≫ f(k,Z)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    P = ((p ⁻¹ᵁ T.toBase.isoLocus).primeDivisorSpanCompl).comap U.picardHom := by
  intro p _ _ _ _
  classical
  let O := T.toBase.isoLocus
  let V := p ⁻¹ᵁ O
  have : Smooth (f(k,X)) := SmoothOfRelativeDimension.smooth 2 (f(k,X))
  have : IsRegular X := IsRegular.of_smooth (f(k,X))
  let := (f(k,X)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two (f(k,X))
  have : IsIntegral Y := hT.isIntegral (f(k,X))
  have hO : O.primeDivisorSpanCompl = ⊥ := by
    have h (q : CodimensionOnePoint X) :
        (q : X) ∉ O ↔ q ∈ Set.range (Empty.elim : Empty → CodimensionOnePoint X) := by
      exact ⟨fun hq ↦ (hq (T.toBase.mem_isoLocus_of_coheight_eq_one q.property)).elim,
        fun ⟨a, _⟩ ↦ a.elim⟩
    rw [O.primeDivisorSpanCompl_eq_span_of_mem_iff _ h]
    simp
  have hIso : IsIso (T.toBase ∣_ O) := T.toBase.le_isoLocus_iff.mp le_rfl
  have : IsIso (p ∣_ O) := by
    dsimp only [p]
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' (inferInstance : IsIso (e.hom ∣_ T.toBase ⁻¹ᵁ O)) hIso
  have hbase (a : Pic(X)) : U.picardHom (E (a, 0)) ∈ V.primeDivisorSpanCompl ↔ a = 0 := by
    rw [picardHom_picardEquivOfCommonResolution, picardHom_apply_zero, pullback_comp,
      ← Submodule.Quotient.mk_eq_zero, ← p.quotientPrimeDivisorSpanComplEquiv_mk O,
      ofMul_toMul, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero, hO,
      Submodule.mem_bot]
  have hsub : P ≤ V.primeDivisorSpanCompl.comap U.picardHom := by
    rw [markedExceptionalSpan_eq_span_range k hT hU e, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, picardHom_picardEquivOfCommonResolution,
      picardHom_apply_single T j 1, zpow_one]
    apply (V.mem_primeDivisorSpanCompl_iff _).mpr
    rw [pullback_comp]
    apply hT.pullback_exceptionalClass_eq_one_of_mapsTo_isoLocus (f(k,X))
    intro a
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply V a]
    simpa only [Scheme.Hom.comp_apply, p, O] using p.mem_preimage.mp a.property
  refine le_antisymm hsub fun x hx ↦ ?_
  obtain ⟨⟨a, b⟩, rfl⟩ := (E).surjective x
  have hb : E (0, b) ∈ P := (mem_markedExceptionalSpan_iff k hT hU e _).mpr
    (by rw [LinearEquiv.symm_apply_apply])
  have hadd : E (a, 0) + E (0, b) = E (a, b) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [← hadd, Submodule.add_mem_iff_left _ (hsub hb), Submodule.mem_comap] at hx
  exact (mem_markedExceptionalSpan_iff k hT hU e _).mpr (by
    rw [LinearEquiv.symm_apply_apply]
    exact (hbase a).mp hx)

end ExceptionalSpan

variable (k : Type u) [Field k] [IsAlgClosed k] [X.Over (Spec (.of k))]
  [Z.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (f(k,X))]
  [SmoothOfRelativeDimension 2 (f(k,Z))] [IsIntegral X] [IsIntegral Z]
  [X.IsProjectiveOver k] [Z.IsProjectiveOver k]
  (hT : IsClosedPointTower X T) (hU : IsClosedPointTower Z U) (e : W ≅ Y)
  (he : e.hom ≫ T.toBase ≫ f(k,X) = U.toBase ≫ f(k,Z))

local notation "B(" S ")" => Chow.intersectionBilinForm k S
local notation "F(" S "," d ")" =>
  LinearMap.BilinForm.prod (B(S)) (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin d → ℤ)))
local notation "noeth(" S ")" => isNoetherian_of_finiteType (f(k,S))
local notation "E" =>
  @picardEquivOfCommonResolution X Y Z W m n T U k _ _ _ _ _ _ _ _ (noeth(X)) (noeth(Z)) hT hU e
local notation "P" => @markedExceptionalSpan X Y Z W m n U k _ _ _ _ _ (noeth(Z)) hU T e
local notation "K" => LinearMap.BilinForm.orthogonal (F(Z,n)) P

include he in
/-- The common-resolution comparison is an isometry of the stabilized Picard forms. -/
def picardIsometryOfCommonResolution : (F(X,m)).IsometryEquiv (F(Z,n)) :=
  { E with
    map_app' := fun a b ↦ by
      simpa only [LinearMap.toFun_eq_coe, LinearEquiv.coe_coe,
       LinearMap.BilinForm.prod_apply, Chow.intersectionBilinForm_apply,
        LinearMap.neg_apply, dotProductBilin_apply_apply, dotProduct, sub_eq_add_neg] using
        classIntersectionNumber_picardEquivOfCommonResolution k hT hU e he a b }

@[simp]
theorem picardIsometryOfCommonResolution_apply (a : Pic(X) × (Fin m → ℤ)) :
    picardIsometryOfCommonResolution k hT hU e he a = E a := (rfl)

include he in
/-- Orthogonality to the contracted exceptional classes is equivalent to vanishing
of the exceptional coordinates in the marking of the contraction tower. -/
theorem mem_orthogonal_markedExceptionalSpan_iff (a : Pic(Z) × (Fin n → ℤ)) :
    a ∈ K ↔ ((E).symm a).2 = 0 := by
  classical
  let : IsNoetherian X := noeth(X)
  let : IsNoetherian Z := noeth(Z)
  let I := picardIsometryOfCommonResolution k hT hU e he
  have hpair (j : Fin m) :
      (F(Z,n)) (E (0, Pi.single j 1)) a = -((E).symm a).2 j := by
    simpa only [I, picardIsometryOfCommonResolution_apply, LinearEquiv.apply_symm_apply,
      LinearMap.BilinForm.prod_apply, Prod.fst_zero, map_zero, LinearMap.zero_apply,
      LinearMap.neg_apply, dotProductBilin_apply_apply, single_one_dotProduct, zero_add]
      using (I.map_app ((E).symm a) (0, Pi.single j 1))
  rw [markedExceptionalSpan_eq_span_range k hT hU e, LinearMap.BilinForm.orthogonal,
    Submodule.mem_orthogonalBilin_span]
  simp only [Set.forall_mem_range, hpair, neg_eq_zero, funext_iff, Pi.zero_apply]

include he in
/-- The marking that identifies the orthogonal complement of the contracted exceptional
span in the coordinates of `U` with the Picard group of the original surface `X`. -/
def contractedPicardMarking : (LinearMap.BilinForm.restrict (F(Z,n)) K).IsometryEquiv (B(X)) where
  toLinearMap := (LinearMap.fst ℤ _ _).comp ((E).symm.toLinearMap.comp (K).subtype)
  invFun a := ⟨E (a, 0), (mem_orthogonal_markedExceptionalSpan_iff k hT hU e he _).mpr
    (by rw [LinearEquiv.symm_apply_apply])⟩
  left_inv a := by
    apply Subtype.ext
    have ha := (mem_orthogonal_markedExceptionalSpan_iff k hT hU e he a.val).mp a.property
    simpa only [LinearMap.toFun_eq_coe, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe, LinearMap.fst_apply, ← ha, Prod.mk.eta] using (E).apply_symm_apply a.val
  right_inv a := by
    simp only [LinearMap.toFun_eq_coe, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe, LinearMap.fst_apply, LinearEquiv.symm_apply_apply]
  map_app' a b := by
    let I := picardIsometryOfCommonResolution k hT hU e he
    have ha := (mem_orthogonal_markedExceptionalSpan_iff k hT hU e he a.val).mp a.property
    have hb := (mem_orthogonal_markedExceptionalSpan_iff k hT hU e he b.val).mp b.property
    simpa only [I, picardIsometryOfCommonResolution_apply, LinearEquiv.apply_symm_apply,
      LinearMap.BilinForm.prod_apply, ha, hb, map_zero,
      LinearMap.zero_apply, LinearMap.neg_apply, neg_zero, add_zero,
      LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply,
      LinearMap.toFun_eq_coe, LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearMap.fst_apply] using (I.map_app ((E).symm b.val) ((E).symm a.val)).symm

/-- The marking recovers the class on the contracted surface as the base coordinate. -/
@[simp]
theorem contractedPicardMarking_apply (a : K) :
    contractedPicardMarking k hT hU e he a = ((E).symm a.val).1 := (rfl)

/-- The inverse marking takes the coordinates of pullback from the contracted surface. -/
theorem coe_contractedPicardMarking_symm_apply (a : Pic(X)) :
    ((contractedPicardMarking k hT hU e he).symm a).val = E (a, 0) := (rfl)

/-- Evaluating the inverse marking on the common surface gives pullback along the
specified contraction, including its identification with the ordered model. -/
@[simp]
theorem picardHom_contractedPicardMarking_symm (a : Pic(X)) :
    U.picardHom ((contractedPicardMarking k hT hU e he).symm a).val =
      Additive.ofMul (pullback (e.hom ≫ T.toBase) a.toMul) := by
  let : IsNoetherian X := isNoetherian_of_finiteType (f(k,X))
  let : IsNoetherian Z := isNoetherian_of_finiteType (f(k,Z))
  rw [coe_contractedPicardMarking_symm_apply, picardHom_picardEquivOfCommonResolution,
    picardHom_apply_zero, pullback_comp]

end QPainleve.BlowupTower
