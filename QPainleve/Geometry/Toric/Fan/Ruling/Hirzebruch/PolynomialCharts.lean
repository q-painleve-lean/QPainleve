/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Gluing
public import QPainleve.Geometry.Toric.Fan.Ruling.ProductCoordinates

/-!
# Hirzebruch rulings from polynomial charts

Two polynomial projective-line charts whose restriction to the Laurent overlap
has the Hirzebruch diagonal transition determine the toric ruling. The isomorphism
agrees with the given maps on both charts, over the original base projective line.
-/

public section

open AlgebraicGeometry CategoryTheory Limits LaurentPolynomial Module
open TauCeti.AlgebraicGeometry (projectiveLine)

namespace TauCeti.Toric.Fan

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => projectiveLine ℂ
local notation "p" => (P ↘ S)
local notation "A" => Polynomial ℂ
local notation "L" => LaurentPolynomial ℂ
local notation "s[" k "]" => Fan.algebraicRealizationStructureMap (projectiveLineAffineFan k)
local notation "l[" k "]" => @projectiveLine.baseChangeProjection A _ L _
  (RingHom.toAlgebra (projectiveLineTorusToAffinePolynomial k))
local notation "P[" k "]" => projectiveLineAffineProductIsoPolynomial k

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {Y : Scheme}
  (b : Basis (Fin 2) ℤ N) (e : ℤ) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun k ↦ (r k).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
  (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (f : Y ⟶ P)

local notation "q" => Fan.characterRuling Φ (LinearMap.toAddMonoidHom (Basis.coord b 1))
  (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "v[" k "]" => Iso.inv (P[k]) ≫ Iso.inv (hirzebruchRulingAffineIso b e r hr hΦ hc k) ≫
  pullback.fst q (projectiveLineAffineFanι k)

/-- The two polynomial projective-line charts of a ruling identify it with a
Hirzebruch ruling when their Laurent overlap scales the first homogeneous
coordinate by `(X₁ / X₀)⁻ᵉ`. The unique comparison respects the base and the
given chart morphisms. -/
theorem existsUnique_hirzebruch_ruling_iso_of_polynomial_charts
    (u : Fin 2 → (projectiveLine A ⟶ Y))
    (hu : ∀ k, IsPullback (u k) (projectiveLine A ↘ Spec (.of A)) f
      (projectiveLine.polynomialChartι ℂ k))
    (hoverlap : l[0] ≫ u 0 =
      (projectiveLine.scalingBy L (LaurentPolynomial.isUnit_T (-e)).unit).hom ≫ l[1] ≫ u 1) :
    ∃! iso : Φ.algebraicRealization ≅ Y,
      iso.hom ≫ f = q ∧ ∀ k, v[k] ≫ iso.hom = u k := by
  let w k := (P[k]).hom ≫ u k
  have hw (k : Fin 2) :
      IsPullback (w k) (pullback.snd p s[k]) f (projectiveLineAffineFanι k) := by
    apply (hu k).of_iso' (P[k]) (Iso.refl _) (projectiveLineAffineFanIso k) (Iso.refl _)
    · simp [w]
    · exact projectiveLineAffineProductIsoPolynomial_hom_toBase k
    · simp
    · simpa using projectiveLineAffineFanIso_hom_comp_polynomialChartι k
  have hscale :
      (hirzebruchRulingOverlapTransition e).hom ≫ projectiveLineTorusPullbackIsoLaurent.hom =
        projectiveLineTorusPullbackIsoLaurent.hom ≫
          (projectiveLine.scalingBy L (LaurentPolynomial.isUnit_T (-e)).unit).hom := by
    rw [projectiveLineTorusPullbackIsoLaurent_def]
    exact hirzebruchRulingOverlapTransition_hom_comp_laurentProduct e
  have hglue : projectiveLineTorusProductToAffine 0 ≫ w 0 =
      (hirzebruchRulingOverlapTransition e).hom ≫ projectiveLineTorusProductToAffine 1 ≫ w 1 := by
    simp only [w, projectiveLineTorusProductToAffine_comp_polynomialIso_assoc, reassoc_of% hscale,
      hoverlap]
  obtain ⟨iso, hiso, huniq⟩ :=
    existsUnique_hirzebruch_ruling_iso_of_overlap_transition f b e r hr hΦ hc w hw hglue
  refine ⟨iso, ⟨hiso.1, fun k ↦ ?_⟩, fun g hg ↦ huniq g ⟨hg.1, fun k ↦ ?_⟩⟩
  · simp only [Category.assoc, hiso.2 k, w, Iso.inv_hom_id_assoc]
  · apply (cancel_epi (P[k]).inv).mp
    simpa only [Category.assoc, w, Iso.inv_hom_id_assoc] using hg.2 k

end TauCeti.Toric.Fan
