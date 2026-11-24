/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Blowup
public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

import QPainleve.AlgebraicGeometry.Blowup.Ample
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Basic
import QPainleve.AlgebraicGeometry.Cohomology.SerreVanishing
import QPainleve.AlgebraicGeometry.IdealSheaf.Quotient
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Comparison
import QPainleve.AlgebraicGeometry.Morphisms.Pullback.IsoLocus
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cohomology
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence

/-!
# Cohomology of an exceptional contraction over an affine base

The ideal of the exceptional fiber is ample because it pulls back from the blowup
along a finite morphism. Serre vanishing and the cohomology of the Cartier layers
then show that every nonnegative ideal power has vanishing first cohomology.
Consequently, pullback of functions from the thickened center to the
thickened exceptional fiber is surjective at each finite level.

The Cartier layers are those of the
[Stacks Project, Lemma 54.16.3](https://stacks.math.columbia.edu/tag/0C2K).
-/

public section

open CategoryTheory Filter MonoidalCategory TopologicalSpace
open TauCeti (isEffectiveCartier_pow cokernelSequence_shortExact)
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

open LineBundleClass

variable {X : Scheme.{u}} {E : X.IdealSheafData}
variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] {I : Y.IdealSheafData}

local notation "powLE" => pow_le_pow_right_of_le_one' (a := E)
  (le_of_le_of_eq le_top (Eq.symm (one_eq_top (X := X))))

section Affine

variable [IsAffine Y]

private theorem isAmple_toInvertibleSheaf_of_contraction (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f] (hI : I.comap f = E)
    (hU : I.support.compl ≤ f.isoLocus) :
    (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf).IsAmple := by
  let H : (I.comap f).IsEffectiveCartier := hI.symm ▸ hE.isEffectiveCartier
  let g := I.blowupLift f H
  have : IsFinite g := hE.isFinite_blowupLift_of_exceptional_contraction f hI hU
  let B := I.isEffectiveCartier_comap_blowupToBase
  have ha := I.eventually_isAmple_pullback_pow_mul_inv_blowupExceptionalClass
    (isAmple_of_isAffine (1 : LineBundleClass Y))
  simp only [pullback_one, one_pow, one_mul, eventually_const, blowupExceptionalClass_def, inv_inv]
    at ha
  have hc : (I.comap I.blowupToBase).comap g = E :=
    (I.comap_blowupLift_exceptional f H).trans hI
  have hb : pullback g (LineBundleClass.mk B.toInvertibleSheaf) =
      LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf :=
    (B.pullback_mk_toInvertibleSheaf (hc.symm ▸ hE.isEffectiveCartier)).trans
      (mk_toInvertibleSheaf_congr _ _ hc)
  rw [← hb]
  exact ha.pullback_of_isAffineHom g

private theorem subsingleton_cohomology_one_thickeningLayer
    (hE : E.IsExceptionalCurveOfFirstKind) (n : ℕ) :
    Subsingleton (Cohomology (Limits.cokernel (sheafHomOfLE (powLE (Nat.le_succ n)))) 1) := by
  obtain ⟨κ, _, e, he⟩ := hE.exists_iso
  have hd : intersectionNumber κ (e.hom ≫ E.subschemeι)
      (LineBundleClass.mk hE.isEffectiveCartier.toInvertibleSheaf) = 1 := by
    rw [intersectionNumber_mk]
    exact (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ 1).mp he
  let N := (isEffectiveCartier_pow hE.isEffectiveCartier n).toInvertibleSheaf
  have hn : -1 ≤ intersectionNumber κ (e.hom ≫ E.subschemeι) (LineBundleClass.mk N) := by
    rw [mk_toInvertibleSheaf_pow hE.isEffectiveCartier n, intersectionNumber_pow_of_isIntegral, hd]
    simp
  let e' := (cohomologyFunctor _ 1).mapIso (hE.isEffectiveCartier.thickeningLayerIso n)
  exact @Function.Injective.subsingleton _ _ _ e'.addCommGroupIsoToAddEquiv.injective
    (E.subsingleton_cohomology_one_tensor_pushforwardSubscheme_of_projectiveLine N e hn)

/-- Over an affine Noetherian base, if a proper morphism is an isomorphism off a closed
subscheme and its scheme-theoretic preimage is an exceptional curve of the first kind,
all nonnegative powers of the exceptional ideal have vanishing first cohomology. -/
theorem subsingleton_cohomology_one_ideal_pow_of_contraction
    (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f] (hI : I.comap f = E)
    (hU : I.support.compl ≤ f.isoLocus) (n : ℕ) :
    Subsingleton (Cohomology (E ^ n).sheaf 1) := by
  let L := hE.isEffectiveCartier.toInvertibleSheaf
  have : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((f ≫ Y.isoSpec.hom).eventually_subsingleton_cohomology_tensorPow_of_isAmple (𝟙_ X.Modules) L
      (hE.isAmple_toInvertibleSheaf_of_contraction f hI hU))
  have hlarge (m : ℕ) (hm : N ≤ m) : Subsingleton (Cohomology (E ^ m).sheaf 1) := by
    let M := (isEffectiveCartier_pow hE.isEffectiveCartier m).toInvertibleSheaf
    have hM : LineBundleClass.mk M = LineBundleClass.mk (L.tensorPow m) :=
      (mk_toInvertibleSheaf_pow hE.isEffectiveCartier m).trans (mk_tensorPow L m).symm
    obtain ⟨e⟩ := mk_eq_mk_iff.mp hM
    let e' := (cohomologyFunctor _ 1).mapIso
      (eqToIso (isEffectiveCartier_pow hE.isEffectiveCartier m).toInvertibleSheaf_obj.symm ≪≫
        e ≪≫ (λ_ (L.tensorPow m).obj).symm)
    exact @Function.Injective.subsingleton _ _ _ e'.addCommGroupIsoToAddEquiv.injective
      (hN m hm 1 Nat.one_pos)
  have hstep (m : ℕ) (hm : Subsingleton (Cohomology (E ^ (m + 1)).sheaf 1)) :
      Subsingleton (Cohomology (E ^ m).sheaf 1) := by
    let a := sheafHomOfLE (powLE (Nat.le_succ m))
    exact subsingleton_cohomology_X₂ (cokernelSequence_shortExact a) 1 hm
      (hE.subsingleton_cohomology_one_thickeningLayer m)
  exact Nat.decreasingInduction'
    (motive := fun m ↦ Subsingleton (Cohomology (E ^ m).sheaf 1))
    (fun m _ _ ↦ hstep m) (le_max_left n N) (hlarge (max n N) (le_max_right n N))

/-- Every regular function on a finite thickening of the exceptional fiber extends to the
source of the contraction over the affine Noetherian base. -/
private theorem surjective_appTop_subschemeι_pow_of_contraction
    (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f] (hI : I.comap f = E)
    (hU : I.support.compl ≤ f.isoLocus) (n : ℕ) :
    Function.Surjective (E ^ n).subschemeι.appTop := by
  intro y
  obtain ⟨x, hx⟩ := sections_surjective (E ^ n).shortExact_toPushforwardSubscheme
    (hE.subsingleton_cohomology_one_ideal_pow_of_contraction f hI hU n) y
  exact ⟨x, ((E ^ n).toPushforwardSubscheme_app (U := ⊤) x).symm.trans hx⟩

end Affine

private theorem surjective_app_comp_subschemeι_pow_of_contraction
    (hE : E.IsExceptionalCurveOfFirstKind) (f : X ⟶ Y) [IsProper f]
    (hI : I.comap f = E) (hU : I.support.compl ≤ f.isoLocus)
    {U : Y.Opens} (hA : IsAffineOpen U) (hS : (I.support : Set Y) ⊆ U)
    [IsIso (f.app U)] (n : ℕ) :
    Function.Surjective (((E ^ (n + 1)).subschemeι ≫ f).app U) := by
  -- Restrict the contraction to the affine neighborhood, retaining the entire exceptional curve.
  let V := f ⁻¹ᵁ U
  let g := f ∣_ U
  let I' := I.comap U.ι
  let E' := E.comap V.ι
  have hCart : E'.IsEffectiveCartier := hE.isEffectiveCartier.comap V.ι
  have hS' : (E.support : Set X) ⊆ V := by
    rw [← hI, support_comap, Closeds.coe_preimage]
    exact Set.preimage_mono hS
  have := E.isIso_subschemeMap_comap_of_support_subset hS'
  have hE' : E'.IsExceptionalCurveOfFirstKind := hE.comap_of_isIso_subschemeMap V.ι hCart
  have hI' : I'.comap g = E' := by
    rw [← comap_comp, morphismRestrict_ι, comap_comp, hI]
  have hU' : I'.support.compl ≤ g.isoLocus := by
    have H := Scheme.Hom.preimage_isoLocus_le_of_isPullback
      (isPullback_morphismRestrict f U)
    calc
      I'.support.compl = U.ι ⁻¹ᵁ I.support.compl := by rw [support_comap]; rfl
      _ ≤ U.ι ⁻¹ᵁ f.isoLocus := U.ι.preimage_mono hU
      _ ≤ g.isoLocus := H
  have : IsAffine U := hA
  have hG : IsIso g.appTop := by
    have H := (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (arrowResLEAppIso f U V le_rfl)
    rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
    exact H.mpr inferInstance
  have he : (E ^ (n + 1)).comap V.ι = E' ^ (n + 1) := E.comap_pow V.ι (n + 1)
  have hsurj := hE'.surjective_appTop_subschemeι_pow_of_contraction g hI' hU' (n + 1)
  rw [← he] at hsurj
  let a := ((E ^ (n + 1)).comap V.ι).subschemeι
  let j := subschemeMap ((E ^ (n + 1)).comap V.ι) (E ^ (n + 1)) V.ι ((E ^ (n + 1)).le_map_comap V.ι)
  -- Compare restriction along the ambient open with restriction along the thickening.
  have hc : (a ≫ g) ≫ U.ι = j ≫ ((E ^ (n + 1)).subschemeι ≫ f) := by
    rw [Category.assoc a, morphismRestrict_ι, ← Category.assoc a, ← Category.assoc j,
      subschemeMap_subschemeι]
  have hs : Function.Surjective (((a ≫ g) ≫ U.ι).app U) := by
    have ht : Function.Surjective ((a ≫ g).app (U.ι ⁻¹ᵁ U)) := by
      rw [U.ι_preimage_self]
      exact hsurj.comp (ConcreteCategory.bijective_of_isIso g.appTop).2
    rw [Scheme.Hom.comp_app]
    have : IsIso (U.ι.app U) := U.ι.isIso_app U (by simp)
    exact ht.comp (ConcreteCategory.bijective_of_isIso (U.ι.app U)).2
  rw [hc, Scheme.Hom.comp_app] at hs
  have hpow : ((E ^ (n + 1)).support : Set X) ⊆ V := (support_pow_succ E n).symm ▸ hS'
  have : IsIso j := (E ^ (n + 1)).isIso_subschemeMap_comap_of_support_subset hpow
  intro y
  let J := j.app (((E ^ (n + 1)).subschemeι ≫ f) ⁻¹ᵁ U)
  obtain ⟨x, hx⟩ := hs (J y)
  exact ⟨x, (ConcreteCategory.bijective_of_isIso J).1 hx⟩

/-- A proper exceptional contraction induces a surjection from the global functions on
the `(n + 1)`st thickening of the center onto those on the corresponding thickening of
the exceptional fiber. Pullback must identify regular functions on an affine neighborhood
of the center with those on its inverse image. -/
theorem surjective_appTop_subschemeMap_pow_of_contraction (hE : E.IsExceptionalCurveOfFirstKind)
    (f : X ⟶ Y) [IsProper f] (hI : I.comap f = E)
    (hU : I.support.compl ≤ f.isoLocus) {U : Y.Opens} (hA : IsAffineOpen U)
    (hS : (I.support : Set Y) ⊆ U) [IsIso (f.app U)] (n : ℕ) :
    Function.Surjective
      (subschemeMap (E ^ (n + 1)) (I ^ (n + 1)) f (pow_le_map_pow hI.le (n + 1))).appTop := by
  let j := subschemeMap (E ^ (n + 1)) (I ^ (n + 1)) f (pow_le_map_pow hI.le (n + 1))
  have hj : j ≫ (I ^ (n + 1)).subschemeι = (E ^ (n + 1)).subschemeι ≫ f :=
    subschemeMap_subschemeι _ _ _ _
  have hs := hE.surjective_app_comp_subschemeι_pow_of_contraction f hI hU hA hS n
  rw [← hj, Scheme.Hom.comp_app] at hs
  have hsurj : Function.Surjective (j.app ((I ^ (n + 1)).subschemeι ⁻¹ᵁ U)) :=
    Function.Surjective.of_comp hs
  have htop : (I ^ (n + 1)).subschemeι ⁻¹ᵁ U = ⊤ := by
    apply top_unique
    intro x _
    apply ((I ^ (n + 1)).subschemeι.mem_preimage).mpr
    apply hS
    rw [← support_pow_succ I n, ← (I ^ (n + 1)).range_subschemeι]
    exact Set.mem_range_self x
  rw [htop] at hsurj
  exact hsurj

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
