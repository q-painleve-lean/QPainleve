/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme

/-!
# Additive coordinates on affine toric charts

The additive semigroup algebra is the coordinate ring used for operations on
integral exponents in the charts of a toric fan.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open AddMonoidAlgebra

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Φ : Fan i) (σ : Φ.cones)

local notation "R" => AddMonoidAlgebra ℂ (dualSemigroup (lattice Φ) (Subtype.val σ))
local notation "e" => toMultiplicativeAlgEquiv ℂ ℂ (dualSemigroup (lattice Φ) (Subtype.val σ))

private def additiveChartIso : Spec (.of R) ≅ Φ.affineToricChart σ :=
  Scheme.Spec.mapIso (e).symm.toRingEquiv.toCommRingCatIso.op

/-- The affine cone chart inclusion in additive semigroup algebra coordinates. -/
def additiveAffineToricChartι : Spec (.of R) ⟶ Φ.algebraicRealization :=
  (additiveChartIso Φ σ).hom ≫ Φ.affineToricChartι σ

/-- Passage to the native affine chart is induced by the additive-to-multiplicative
monoid algebra equivalence. -/
theorem additiveAffineToricChartι_def :
    Φ.additiveAffineToricChartι σ =
      Spec.map (CommRingCat.ofHom (e).symm.toRingEquiv.toRingHom) ≫ Φ.affineToricChartι σ :=
  (rfl)

instance isOpenImmersion_additiveAffineToricChartι :
    IsOpenImmersion (Φ.additiveAffineToricChartι σ) := by
  unfold additiveAffineToricChartι
  infer_instance

/-- The additive and native inclusions have the same open image. -/
@[simp]
theorem range_additiveAffineToricChartι :
    Set.range (Φ.additiveAffineToricChartι σ) = Set.range (Φ.affineToricChartι σ) := by
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange]
  exact congrArg SetLike.coe (Scheme.Hom.opensRange_comp_of_isIso
    (additiveChartIso Φ σ).hom (Φ.affineToricChartι σ))

end TauCeti.Toric.Fan
