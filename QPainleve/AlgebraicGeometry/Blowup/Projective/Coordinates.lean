/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.UniversalProperty
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.CoordinateMap
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop

/-!
# Homogeneous coordinates of an affine ideal blowup

An indexed family generating an ideal gives homogeneous coordinates of the blowup.
The coordinates have the same indices as the family, even if generators are repeated.
This makes it possible to compare them with sections in a projective linear system.

## References

* [The Stacks Project, Lemma 31.33.13](https://stacks.math.columbia.edu/tag/02NS).
* Mathlib's `adjoin_monomial_eq_reesAlgebra` and Tau Ceti's `projReesAlgebra_hom_ext`.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open TauCeti TauCeti.AlgebraicGeometry

namespace reesAlgebra

universe u

variable {R : Type u} [CommRing R] {I : Ideal R} {ι : Type u}
  (a : ι → I)

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒫" => MvPolynomial.homogeneousSubmodule ι R
local notation "ℬ" => grade I

private def generators : ι → reesAlgebra I :=
  fun i ↦ monomialDegreeOne (a i).property

/-- Evaluation at the degree-one Rees monomials of an indexed family in the ideal. -/
private def coordinateHom : 𝒫 →ₐᵍ[R] ℬ :=
  ⟨MvPolynomial.aeval (generators a), fun hp ↦
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp).aeval_mem
      (fun i ↦ monomialDegreeOne_mem_grade (a i).property)⟩

/-- Each variable maps to its chosen generator times the Rees parameter. -/
@[simp]
private theorem coordinateHom_X (i : ι) :
    coordinateHom a (.X i) = monomialDegreeOne (a i).property :=
  MvPolynomial.aeval_X _ _

/-- Constants map to degree-zero coefficients. -/
@[simp]
private theorem coordinateHom_C (r : R) :
    coordinateHom a (.C r) = algebraMap R (reesAlgebra I) r :=
  MvPolynomial.aeval_C _ _

/-- The homogeneous coordinate homomorphism is surjective for a generating family. -/
private theorem coordinateHom_surjective (ha : Ideal.span (Set.range fun i ↦ (a i : R)) = I) :
    Function.Surjective (coordinateHom a) := by
  -- Read the graded evaluation as its underlying algebra homomorphism.
  change Function.Surjective (MvPolynomial.aeval (generators a))
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  apply (Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective)
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  calc
    _ = Algebra.adjoin R (Submodule.map (Polynomial.monomial 1 : R →ₗ[R] Polynomial R)
        (Submodule.span R (Set.range fun i ↦ (a i : R))) : Set (Polynomial R)) := by
      simp only [Submodule.map_span, Algebra.adjoin_span, ← Set.range_comp, Function.comp_def,
        generators, Subalgebra.val_apply, coe_monomialDegreeOne]
    _ = reesAlgebra I := by
      rw [Ideal.submodule_span_eq, ha, adjoin_monomial_eq_reesAlgebra]

private theorem irrelevant_le_map_coordinateHom
    (ha : Ideal.span (Set.range fun i ↦ (a i : R)) = I) :
    HomogeneousIdeal.irrelevant ℬ ≤
      (HomogeneousIdeal.irrelevant 𝒫).map (coordinateHom a).toGradedRingHom :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective _ (coordinateHom_surjective a ha)

/-- The embedding of the affine blowup with coordinates indexed by the generating family. -/
def coordinateEmbedding (ha : Ideal.span (Set.range fun i ↦ (a i : R)) = I) :
    Proj ℬ ⟶ Proj 𝒫 :=
  Proj.map (coordinateHom a).toGradedRingHom (irrelevant_le_map_coordinateHom a ha)

instance (ha : Ideal.span (Set.range fun i ↦ (a i : R)) = I) :
    IsClosedImmersion (coordinateEmbedding a ha) :=
  Proj.isClosedImmersion_map _ _ (coordinateHom_surjective a ha)

/-- Pulling back the coefficient morphism recovers the affine blowup projection. -/
@[reassoc (attr := simp)]
theorem coordinateEmbedding_toSpecCoeff
    (ha : Ideal.span (Set.range fun i ↦ (a i : R)) = I) :
    coordinateEmbedding a ha ≫ Proj.toSpecCoeff 𝒫 = Proj.toSpecCoeff ℬ := by
  rw [coordinateEmbedding]
  apply Proj.map_toSpecCoeff
  intro r
  apply Subtype.ext
  simp [SetLike.GradeZero.coe_algebraMap]

/-- The inverse image of a coordinate open is the indicated Rees standard open. -/
@[simp]
theorem coordinateEmbedding_preimage_basicOpen
    (ha : Ideal.span (Set.range fun i ↦ (a i : R)) = I) (i : ι) :
    coordinateEmbedding a ha ⁻¹ᵁ Proj.basicOpen 𝒫 (.X i) =
      Proj.basicOpen ℬ (monomialDegreeOne (a i).property) := by
  rw [coordinateEmbedding, Proj.map_preimage_basicOpen]
  exact congrArg (Proj.basicOpen ℬ) (coordinateHom_X a i)

private def evaluationAtOne : reesAlgebra I →ₐ[R] R :=
  (Polynomial.aeval (1 : R)).comp (reesAlgebra I).val

@[simp] private theorem evaluationAtOne_monomialDegreeOne {x : R} (hx : x ∈ I) :
    evaluationAtOne (monomialDegreeOne hx) = x := by
  simp [evaluationAtOne, coe_monomialDegreeOne]

variable {T : Scheme.{u}} (b : R →+* Γ(T, ⊤))

private theorem map_irrelevant_evaluationAtOne
    (ha : Ideal.span (Set.range fun i ↦ (a i : R)) = I) (hb : I.map b = ⊤) :
    (HomogeneousIdeal.irrelevant ℬ).toIdeal.map
      (b.comp (evaluationAtOne (I := I)).toRingHom) = ⊤ := by
  calc
    _ = (Ideal.span (Set.range fun i ↦ (a i : R))).map b := by
      rw [irrelevant_eq_span_monomialDegreeOne ha, Ideal.map_span, Ideal.map_span,
        ← Set.range_comp, ← Set.range_comp]
      congr 1
      exact congrArg Set.range (funext fun i ↦
        congrArg b (evaluationAtOne_monomialDegreeOne (a i).property))
    _ = ⊤ := (congrArg (Ideal.map b) ha).trans hb

private theorem fromOfGlobalSections_evaluationAtOne_toSpecCoeff
    (ha : Ideal.span (Set.range fun i ↦ (a i : R)) = I) (hb : I.map b = ⊤) :
    Proj.fromOfGlobalSections ℬ (b.comp (evaluationAtOne (I := I)).toRingHom)
        (map_irrelevant_evaluationAtOne a b ha hb) ≫ Proj.toSpecCoeff ℬ =
      T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b) := by
  rw [Proj.toSpecCoeff_def, Proj.fromOfGlobalSections_toSpecZero_assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp [SetLike.GradeZero.coe_algebraMap]

/-- Where the generators give the unit ideal, the indexed Rees embedding evaluates to
the ordinary homogeneous coordinates of the generators. The equality is an equality
of scheme morphisms over the coefficient ring. -/
theorem comp_coordinateEmbedding_eq_fromOfGlobalSections
    (ha : Ideal.span (Set.range fun i ↦ (a i : R)) = I) (hb : I.map b = ⊤)
    (g : T ⟶ Proj ℬ)
    (hg : g ≫ Proj.toSpecCoeff ℬ = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom b)) :
    ∃ h : (HomogeneousIdeal.irrelevant 𝒫).toIdeal.map (eval₂Hom b fun i ↦ b (a i)) = ⊤,
      g ≫ coordinateEmbedding a ha =
        Proj.fromOfGlobalSections 𝒫 (eval₂Hom b fun i ↦ b (a i)) h := by
  let v := b.comp (evaluationAtOne (I := I)).toRingHom
  have hv := map_irrelevant_evaluationAtOne a b ha hb
  have hg' : g = Proj.fromOfGlobalSections ℬ v hv := by
    apply projReesAlgebra_hom_ext
    · simp only [← toSpecCoeff_reesAlgebra, hg,
        fromOfGlobalSections_evaluationAtOne_toSpecCoeff a b ha hb, v]
    · rw [← toSpecCoeff_reesAlgebra, hg,
        Scheme.IdealSheafData.comap_comp,
        Scheme.IdealSheafData.comap_ofIdealTop_map_ΓSpecIso_inv,
        Scheme.IdealSheafData.comap_ofIdealTop, CommRingCat.hom_ofHom, hb]
      rw [Ideal.map_top, Ideal.map_top]
      have htop : Scheme.IdealSheafData.ofIdealTop (⊤ : Ideal Γ(T, ⊤)) = ⊤ := by
        ext1
        funext U
        simp [Ideal.map_top]
      exact htop ▸ Scheme.IdealSheafData.isEffectiveCartier_top T
  rw [hg', coordinateEmbedding, Proj.fromOfGlobalSections_map]
  have he : v.comp (coordinateHom a).toGradedRingHom.toRingHom =
      eval₂Hom b (fun i ↦ b (a i)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [v]
    · intro i
      simp [v]
  have hh : (HomogeneousIdeal.irrelevant 𝒫).toIdeal.map (eval₂Hom b fun i ↦ b (a i)) = ⊤ := by
    rw [irrelevant_eq_span_X, Ideal.map_span, ← Set.range_comp]
    have hgen := (congrArg (Ideal.map b) ha).trans hb
    rw [Ideal.map_span, ← Set.range_comp] at hgen
    simpa only [Function.comp_def, eval₂Hom_X'] using hgen
  exact ⟨hh, by congr 1⟩

end reesAlgebra
