/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Normalization
public import QPainleve.Geometry.Toric.Fan.Boundary.Prime

/-!
# Numbered ray primes of ordered toric blowups

The generic point of a numbered component of the reduced toric boundary gives the
corresponding ray prime of the strict boundary in the ordered internal blowup.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "D" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h₀)
local notation "ν" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus ℂ D)

variable [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ Spec (.of ℂ))] {r : ℕ}

/-- The strict boundary prime indexed by a ray is the image of the generic point
of the corresponding normalization component. -/
theorem internalBlowupBoundaryPrime_val (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N)
    (s : Fin r → Φ.Ray) (c : Fin r → ℂˣ) (ρ : Φ.Ray) :
    (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ).val =
      (internalBlowupTower b s c).2.boundaryι
        (ν (genericPoints.ofComponent (Φ.boundaryNormalizationComponentEquiv hΦ ρ))) := by
  let v := Φ.boundaryNormalizationComponentEquiv hΦ ρ
  let jD := (internalBlowupTower b s c).2.boundaryι
  have hray := Φ.range_boundaryNormalizationComponentEquiv hΦ ρ
  have hr : Set.range (((D).blowupComponent (K := ℂ) v).ι ≫ ν ≫ jD) =
      Set.range (ρ.boundaryComponentι hΦ ≫ jD) := by
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.image_comp] using
      congrArg (fun Z ↦ jD '' Z) hray
  rw [(D).range_blowupComponent_comp (k := ℂ) v jD jD.isClosedMap,
    range_rayComponent_internalBlowupBoundaryPrimeEquiv] at hr
  exact isGenericPoint_closure.eq (hr ▸ isGenericPoint_closure)

end TauCeti.Toric.Fan
