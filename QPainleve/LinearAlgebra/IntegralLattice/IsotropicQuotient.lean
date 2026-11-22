/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import QPainleve.LinearAlgebra.BilinearForm.IsotropicQuotient
public import QPainleve.LinearAlgebra.IntegralLattice.RadicalQuotient
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Radical quotient of an isotropic vector's orthogonal complement

For a primitive isotropic vector in a perfect symmetric integral form, the radical of the
form on its orthogonal complement is the isotropic line. The comparison identifies the
orthogonal quotient form with Tau Ceti's integral radical quotient.
-/

public section

open Submodule LinearMap TauCeti.IntegralLattice
open scoped TensorProduct

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
  {B : LinearMap.BilinForm ℤ M} [B.IsPerfPair] {δ : M}

local notation "W" => B.orthogonal (ℤ ∙ δ)
local notation "P" => Submodule.comap (Submodule.subtype W) (ℤ ∙ δ)

/-- The rationalized form on the orthogonal complement of a primitive isotropic vector
has radical the rational line of that vector. -/
theorem IsSymm.radical_ofIntegralForm_restrict_orthogonal (hB : B.IsSymm)
    (hδ : B δ δ = 0) (hprim : TauCeti.IsPrimitive δ) :
    (ofIntegralForm (B.restrict W) (hB.restrict W)).radical =
      ℚ ∙ ((1 : ℚ) ⊗ₜ[ℤ] (⟨δ, by
        rw [BilinForm.orthogonal, Submodule.orthogonalBilin_span_singleton, mem_ker]
        exact hδ⟩ : W)) := by
  let x : W := ⟨δ, by
    rw [BilinForm.orthogonal, Submodule.orthogonalBilin_span_singleton, mem_ker]
    exact hδ⟩
  have hline : P = ℤ ∙ x := by
    rw [← (Submodule.comap_map_eq_of_injective (W).injective_subtype (ℤ ∙ x)),
      Submodule.map_span, Set.image_singleton, Submodule.subtype_apply]
  rw [ofIntegralForm.radical_eq_baseChange_ker, B.ker_restrict_orthogonal_of_isPrimitive hprim,
    hline, Submodule.baseChange_span, Set.image_singleton, TensorProduct.mk_apply]

/-- The orthogonal quotient for a primitive vector agrees with the integral form
of the native radical quotient of its orthogonal complement. -/
noncomputable def IsSymm.orthogonalQuotientIsometryRadicalQuotient (hB : B.IsSymm)
    (hprim : TauCeti.IsPrimitive δ) :
    (B.orthogonalQuotientForm hB (ℤ ∙ δ)).IsometryEquiv
      (ofIntegralForm (B.restrict W) (hB.restrict W)).radicalQuotient.integralForm := by
  let e := ofIntegralForm.radicalQuotientIsometry (hB.restrict W) P
    (B.ker_restrict_orthogonal_of_isPrimitive hprim).symm
  refine ⟨e.toLinearEquiv, fun x y ↦ ?_⟩
  obtain ⟨x, rfl⟩ := (P).mkQ_surjective x
  obtain ⟨y, rfl⟩ := (P).mkQ_surjective y
  simp [e]

/-- The comparison sends an orthogonal quotient representative to its radical quotient class. -/
@[simp]
theorem IsSymm.orthogonalQuotientIsometryRadicalQuotient_mk (hB : B.IsSymm)
    (hprim : TauCeti.IsPrimitive δ) (x : W) :
    hB.orthogonalQuotientIsometryRadicalQuotient hprim (Submodule.Quotient.mk x) =
      (ofIntegralForm (B.restrict W) (hB.restrict W)).radicalQuotientMap
        (ofIntegralForm.carrierEquiv (B.restrict W) (hB.restrict W) x) := by
  rw [← BilinForm.IsometryEquiv.coe_toLinearEquiv]
  simp [orthogonalQuotientIsometryRadicalQuotient, BilinForm.IsometryEquiv.coe_toLinearEquiv]

end LinearMap.BilinForm
