/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.FaceLocalization
public import TauCeti.Geometry.Toric.Algebraic.Fan.DenseTorus

/-!
# Density of the torus in a toric scheme

The inclusion of a face induces an injective map of affine toric coordinate rings, so
the corresponding open immersion is dominant. Applying this to the zero face in each
chart shows that Tau Ceti's torus inclusion is dense in any nonempty fan realization.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.Fan

universe u

variable {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- The torus inclusion in the scheme of a nonempty fan is dominant. -/
instance isDominant_denseTorusι (Φ : Fan i) (hΦ : Nonempty Φ.cones) :
    IsDominant (Φ.denseTorusι hΦ) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨σ, y, rfl⟩ := Φ.exists_affineToricChartι_apply_eq x
  let hface := (Φ.isToricCone σ.2).salient.bot_isFaceOf
  have hdense := (isDominant_faceAffineToricSchemeMap Φ.lattice hface).denseRange
  have hclosure := (Φ.affineToricChartι σ).continuous.range_subset_closure_image_dense hdense
  have hcomp : ⇑(faceAffineToricSchemeMap Φ.lattice hface ≫ Φ.affineToricChartι σ) =
      ⇑(Φ.affineToricChartι σ) ∘ ⇑(faceAffineToricSchemeMap Φ.lattice hface) :=
    funext (Scheme.Hom.comp_apply _ _)
  rw [← Set.range_comp, ← hcomp, ← Φ.denseTorusι_face σ] at hclosure
  exact hclosure ⟨y, rfl⟩

end TauCeti.Toric.Fan
