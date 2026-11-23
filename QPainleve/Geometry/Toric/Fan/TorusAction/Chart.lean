/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.TorusAction.Translation

import QPainleve.Geometry.Toric.Fan.Separated

/-!
# Torus translations on affine fan charts

The restriction of a translation to any cone chart acts on regular monomials by
the corresponding character twist. This extends the dense-torus comparison to
charts meeting the toric boundary.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative

namespace TauCeti.Toric.Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- Translation on the chart of a cone is induced by the character twist on its affine
semigroup algebra. -/
theorem affineToricChartι_comp_torusTranslation_hom [Nonempty Φ.cones]
    (σ : Φ.cones) (χ : Multiplicative (N →+ ℤ) →* ℂˣ) :
    Φ.affineToricChartι σ ≫ (Φ.torusTranslation χ).hom =
      Spec.map (CommRingCat.ofHom (MonoidAlgebra.charTwist
        (χ.comp ((dualSemigroup Φ.lattice σ.val).subtype.toMultiplicative))).toAlgHom.toRingHom) ≫
          Φ.affineToricChartι σ := by
  let h := (Φ.isToricCone σ.property).salient.bot_isFaceOf
  let f := faceAffineToricSchemeMap Φ.lattice h
  have := isDominant_faceAffineToricSchemeMap Φ.lattice h
  apply AlgebraicGeometry.ext_of_isDominant f
  have hcomp := Φ.denseTorusι_face σ
  rw [← Category.assoc, ← hcomp, Φ.denseTorusι_comp_torusTranslation_hom χ,
    hcomp, ← Category.assoc, ← Category.assoc]
  dsimp only [f]
  rw [faceAffineToricSchemeMap_def, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  let r := faceAffineCoordinateRingMap Φ.lattice h
  let t₀ := MonoidAlgebra.charTwist (k := ℂ)
    (χ.comp (denseTorusDualEquiv Φ.lattice).toMultiplicative.toMonoidHom)
  let tσ := MonoidAlgebra.charTwist (k := ℂ)
    (χ.comp (dualSemigroup Φ.lattice σ.val).subtype.toMultiplicative)
  suffices t₀.toAlgHom.comp r = r.comp tσ.toAlgHom from
    CommRingCat.hom_ext (congrArg AlgHom.toRingHom this)
  apply MonoidAlgebra.algHom_ext
  · intro a
    obtain ⟨m, rfl⟩ : ∃ m, ofAdd m = a := ⟨a.toAdd, ofAdd_toAdd a⟩
    simp [r, t₀, tσ, MonoidAlgebra.charTwist_single]
  · exact Subsingleton.elim _ _

end TauCeti.Toric.Fan
