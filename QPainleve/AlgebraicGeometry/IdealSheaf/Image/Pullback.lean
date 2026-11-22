/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.IdealSheaf.Image
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Image
import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Pullback

/-!
# Pullback of image ideal sheaves

The image ideal of a quasicoherent module mapped to the structure sheaf commutes
with arbitrary base change. The proof uses Tau Ceti's
`imageIdealSheaf_eq_fittingIdeal_cokernel` and `fittingIdeal_pullback`.
See [The Stacks Project, Section 31.9](https://stacks.math.columbia.edu/tag/0C3C).
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- Pulling back a functional on a quasicoherent sheaf pulls back its image ideal sheaf. -/
theorem imageIdealSheaf_pullback {X Y : Scheme.{u}} {M : Y.Modules} [M.IsQuasicoherent]
    (φ : M ⟶ 𝟙_ Y.Modules) (f : X ⟶ Y) :
    ((Scheme.Modules.pullback f).map φ ≫
      (Scheme.Modules.pullbackObjUnitIso f).hom).imageIdealSheaf = φ.imageIdealSheaf.comap f := by
  let P := Scheme.Modules.pullback f
  let u := Scheme.Modules.pullbackObjUnitIso f
  let e : P.obj (cokernel φ) ≅ cokernel (P.map φ ≫ u.hom) :=
    PreservesCokernel.iso P φ ≪≫
      cokernel.mapIso (P.map φ) (P.map φ ≫ u.hom) (Iso.refl _) u (by simp)
  rw [imageIdealSheaf_eq_fittingIdeal_cokernel, imageIdealSheaf_eq_fittingIdeal_cokernel,
    ← Scheme.Modules.fittingIdeal_pullback]
  exact (Scheme.Modules.fittingIdeal_congr
    (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.val U.property) e 0).symm

end AlgebraicGeometry.Scheme.Modules.Hom
