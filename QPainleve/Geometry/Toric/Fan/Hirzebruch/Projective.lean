/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ray
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over

import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
import QPainleve.Geometry.Toric.Fan.Ruling.Quadric
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Descent
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Hirzebruch

/-!
# Projectivity of Hirzebruch fans

A complete regular fan in Hirzebruch form has projective algebraic realization.
Toric elementary transformations connect it to the quadric through common point blowups.
The result applies to either choice of section in the ray frame.
-/

public section

open AlgebraicGeometry Module
open TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

private theorem isProjectiveOver_hirzebruch_neg_natCast
    (a : ℕ) (Φ : Fan i) (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, -(a : ℤ) • b 0 - b 1}) :
    Φ.algebraicRealization.IsProjectiveOver ℂ := by
  induction a generalizing Φ b with
  | zero =>
    obtain ⟨r, hr⟩ := exists_rayEquiv_of_hirzebruch_ray_generators b 0 (by simpa using hrays)
    exact Φ.isProjectiveOver_quadric b hΦ hc r hr
  | succ a ih =>
    obtain ⟨Ψ, _, hΨ, _, hcΨ, _, d, σ, τ, s, t, g, g', _, _, _, _, _, hΨrays, _, _,
      hg, hg', -⟩ := Φ.exists_blowup_span_hirzebruch_toric_elementary_transformation
      b hΦ hc (-(↑(a + 1) : ℤ)) hrays
    have hindex : -(↑(a + 1) : ℤ) + 1 = -(a : ℤ) := by omega
    let : Ψ.algebraicRealization.IsProjectiveOver ℂ :=
      ih Ψ d hΨ hcΨ (by simpa only [hindex] using hΨrays)
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (CommRingCat.of ℂ)) :=
      (Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)) ▸
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    exact s.isProjectiveOver_of_common_pointBlowup t τ σ g' g hg' hg

/-- The algebraic realization of a complete regular Hirzebruch fan is projective
over `ℂ` for any signed Hirzebruch parameter. -/
theorem isProjectiveOver_hirzebruch (Φ : Fan i)
    (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1]) :
    Φ.algebraicRealization.IsProjectiveOver ℂ := by
  have projective (a : ℕ) (d : Basis (Fin 2) ℤ N) (t : Fin 4 ≃ Φ.Ray)
      (ht : (fun j ↦ (t j).primitiveGenerator) = ![d 0, d 1, -d 0, -(a : ℤ) • d 0 - d 1]) :
      Φ.algebraicRealization.IsProjectiveOver ℂ := by
    apply isProjectiveOver_hirzebruch_neg_natCast a Φ d hΦ hc
    rw [← t.surjective.range_comp, Function.comp_def, ht]
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rcases e.eq_nat_or_neg with ⟨a, rfl | rfl⟩
  · obtain ⟨d, t, ht, -, -⟩ := Φ.exists_hirzebruch_opposite_section_basis b a r hr
    exact projective a d t ht
  · exact projective a b r hr

end TauCeti.Toric.Fan
