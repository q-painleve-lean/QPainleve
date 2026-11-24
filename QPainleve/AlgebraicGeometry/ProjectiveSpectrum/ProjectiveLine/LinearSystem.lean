/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cohomology
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Twist
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction
import QPainleve.AlgebraicGeometry.LineBundle.Pullback
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.GlobalGeneration
import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
import TauCeti.AlgebraicGeometry.Cohomology.Genus
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.ZeroLocus

/-!
# Linear systems of projective-line divisors

If an effective Cartier divisor is a projective line with nonnegative normal degree,
vanishing of the ambient first structure-sheaf cohomology lets its normal sections lift.
This gives the dimension and global generation of the complete linear system used in
[Vakil, *Complex Algebraic Surfaces*, Class 17, §2][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf
-/

public section

open CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules LineBundleClass

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {I : X.IdealSheafData}

local notation "S" => Spec (CommRingCat.of k)
local notation "O(" h ")" => InvertibleSheaf.dual (IsEffectiveCartier.toInvertibleSheaf h)

private noncomputable def dualTensorIdealIso (hI : I.IsEffectiveCartier) :
    (O(hI)).obj ⊗ I.sheaf ≅ (InvertibleSheaf.trivial X).obj :=
  (whiskerRightIso (InvertibleSheaf.tensorTrivialLeftIsoSheaf (O(hI))) I.sheaf).symm ≪≫
    hI.tensorDualCancelIso (InvertibleSheaf.trivial X)

omit [X.Over (Spec (.of k))] in
private theorem isGloballyGenerated_dual_of_projectiveLine
    (hI : I.IsEffectiveCartier) (e : projectiveLine k ≅ I.subscheme)
    (h₁ : Subsingleton (Cohomology ((O(hI)).obj ⊗ I.sheaf) 1))
    (hdeg : 0 ≤ intersectionNumber k (e.hom ≫ I.subschemeι) (LineBundleClass.mk (O(hI)))) :
    (O(hI)).IsGloballyGenerated := by
  let L := O(hI)
  let M := (InvertibleSheaf.pullback I.subschemeι).obj L
  have hd : 0 ≤ ((InvertibleSheaf.pullback e.hom).obj M).eulerDegree k := by
    rw [← eulerDegree_mk, ← pullback_mk, ← pullback_mk, pullback_comp,
      ← intersectionNumber_def]
    exact hdeg
  have hM := M.isGloballyGenerated_of_nonneg_eulerDegree_projectiveLine e hd
  have hlift := I.surjective_pullbackSectionsLE_of_subsingleton_cohomology_one L h₁
  refine InvertibleSheaf.isGloballyGenerated_iff.mpr fun x ↦ ?_
  by_cases hx : x ∈ I.support
  · obtain ⟨y, rfl⟩ := I.range_subschemeι.ge hx
    obtain ⟨t, ht⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp hM y
    let a := eqToIso (InvertibleSheaf.pullback_obj_obj I.subschemeι L)
    obtain ⟨s, hs⟩ := hlift (a.hom.app ⊤ t)
    have ht' : y ∈ ((Scheme.Modules.pullback I.subschemeι).obj L.obj).nonvanishingLocus
        (a.hom.app ⊤ t) := by
      rwa [nonvanishingLocus_hom_app]
    rw [← hs, nonvanishingLocus_pullbackSectionsLE, top_inf_eq] at ht'
    exact ⟨s, I.subschemeι.mem_preimage.mp ht'⟩
  · obtain ⟨s, hs⟩ := hI.exists_zeroIdeal_eq_dual
    exact ⟨s, (L.mem_nonvanishingLocus_iff_notMem_support_zeroIdeal s x).mpr (hs.symm ▸ hx)⟩

/-- A projective-line Cartier divisor of normal degree `d ≥ 0` on an integral projective
scheme with `H¹(𝒪) = 0` has a base-point-free complete linear system of dimension
`d + 1`. The underlying line bundle has `d + 2` independent global sections. -/
theorem isGloballyGenerated_and_finrank_globalSections_dual_of_projectiveLine [X.IsProjectiveOver k]
    [IsIntegral X] (hI : I.IsEffectiveCartier)
    (e : projectiveLine k ≅ I.subscheme) [e.hom.IsOver S]
    (h₁ : Subsingleton (Cohomology (InvertibleSheaf.trivial X).obj 1)) {d : ℕ}
    (hdeg : intersectionNumber k (e.hom ≫ I.subschemeι) (LineBundleClass.mk (O(hI))) = d) :
    (O(hI)).IsGloballyGenerated ∧ Module.finrank k Γ((O(hI)).obj, ⊤) = d + 2 := by
  let L := O(hI)
  let c := hI.dualTensorIdealIso
  let _ := h₁
  have hvan : Subsingleton (Cohomology (L.obj ⊗ I.sheaf) 1) :=
    (cohomologyBaseLinearEquivOfIso k c 1).injective.subsingleton
  refine ⟨hI.isGloballyGenerated_dual_of_projectiveLine e hvan (hdeg ▸ Int.natCast_nonneg d), ?_⟩
  let σ := projectiveLine.infinitySection k ≫ e.hom ≫ I.subschemeι
  have hσ : σ ≫ X ↘ S = 𝟙 S := by simp [σ, comp_over]
  have hconstants : Function.Surjective (baseRingToGlobalSections k X) := by
    rw [funext (baseRingToGlobalSections_apply k X)]
    exact (appTop_bijective_of_section hσ).surjective.comp
      (ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective
  have hleft : Module.finrank k (Cohomology (L.obj ⊗ I.sheaf) 0) = 1 := by
    rw [(cohomologyBaseLinearEquivOfIso k c 0).finrank_eq,
      finrank_cohomology_zero_trivial_eq_one_of_surjective k hconstants]
  have hright : Module.finrank k (Cohomology (L.obj ⊗ I.pushforwardSubscheme) 0) = d + 1 := by
    rw [(I.cohomologyTensorPushforwardSubschemeEquivTwistingSheaf e L 0).finrank_eq, hdeg,
      projectiveLine.finrank_cohomology_zero_twistingSheaf]
    omega
  have hfinite (q : ℕ) : Module.Finite k (Cohomology (L.obj ⊗ 𝟙_ X.Modules) q) := by
    have := moduleFinite_cohomology_of_isProjectiveOver k L.obj q
    exact Module.Finite.of_surjective _
      (cohomologyBaseLinearEquivOfIso k (ρ_ L.obj).symm q).surjective
  have hadd := eulerCharBelow_eq_add k (I.shortExact_tensor_toPushforwardSubscheme L.obj) 1
    (fun _ hi hj ↦ (by omega : False).elim) (fun q _ ↦ hfinite q) hvan
  -- The short exact sequence is obtained by tensoring the ideal sequence by L.
  change eulerCharBelow k X (L.obj ⊗ 𝟙_ X.Modules) 1 =
    eulerCharBelow k X (L.obj ⊗ I.sheaf) 1 +
      eulerCharBelow k X (L.obj ⊗ I.pushforwardSubscheme) 1 at hadd
  simp only [eulerCharBelow_succ, eulerCharBelow_zero, pow_zero, one_mul, zero_add] at hadd
  rw [hleft, hright, finrank_cohomology_congr k (ρ_ L.obj) 0,
    finrank_cohomology_zero_eq_finrank_globalSections] at hadd
  dsimp only [L] at hadd
  omega

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
