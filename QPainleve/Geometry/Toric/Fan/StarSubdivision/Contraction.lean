/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization
public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary

import QPainleve.Geometry.Toric.Cone.Coordinates
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.StarSubdivision.TwoDimensional
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Inverse star subdivisions of toric surfaces

A boundary curve of square `-1` on a regular complete toric surface arises from
subdividing the cone spanned by its two neighboring rays. The new fan replaces
the two incident cones by that single regular cone. The identified ray is the
exceptional ray of the subdivision.

This is the fan calculation for the contraction of a torus-invariant exceptional
curve, as in Cox, Little and Schenck, *Toric Varieties*, §10.4.
-/

public noncomputable section

open PointedCone Module
open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

/-- A ray of boundary self-intersection `-1` in a complete regular toric surface
is the inserted ray of a star subdivision of a complete regular fan. The
subdivision is along a two-ray cone, and recovers the given fan on its lattice. -/
theorem exists_star_subdivision_of_ray_self_intersection_neg_one
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Φ.Ray)
    (hself : Φ.rayBoundarySelfIntersection hΦ r = -1) :
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (σ : Ψ.cones)
      (hσ : Nat.card (ToricRay σ.val) = 2),
      Ψ.IsComplete ∧ Ψ.starSubdivisionAlong hΨ σ.property = Φ ∧
        (Ψ.starSubdivisionAlongRay hΨ σ.property (ne_bot_of_card_toricRay_eq_two hσ)).toCone.val =
          r.toCone.val := by
  obtain ⟨p, q, hpDet, hqDet, hn, hsum⟩ :=
    exists_rayBoundaryPoint_selfIntersection_relation b hΦ hc r
  rw [← rayBoundarySelfIntersection_def, hself, neg_one_zsmul] at hsum
  have hsum' : p.primitiveGenerator + q.primitiveGenerator = r.primitiveGenerator := by
    calc
      _ = (p.primitiveGenerator + -r.primitiveGenerator + q.primitiveGenerator) +
          r.primitiveGenerator := by abel
      _ = _ := by rw [hsum, zero_add]
  have hp : b.detDualEquiv p.primitiveGenerator r.primitiveGenerator = 1 := by
    rw [b.detDualEquiv_swap]
    omega
  obtain ⟨_, C, hrC, hpC⟩ := (hn p).mpr (Or.inl rfl)
  obtain ⟨_, D, hrD, hqD⟩ := (hn q).mpr (Or.inr rfl)
  obtain ⟨Ψ, hΨ, σ, hσ, hc', hstar, hr, -⟩ :=
    exists_star_subdivision_of_ray_eq_sum b hΦ hc ⟨hp, C, hpC, hrC⟩
      ⟨hqDet, D, hrD, hqD⟩ hsum'
  exact ⟨Ψ, hΨ, σ, hσ, hc', hstar, hr⟩

/-- A toric boundary divisor of square `-1` is the exceptional divisor of the
blowup of a distinguished point of another smooth complete toric surface. The
blowup identification matches the reduced total transform of the toric boundary. -/
theorem exists_iso_blowup_of_ray_self_intersection_neg_one
    [Φ.algebraicRealization.IsProjectiveOver ℂ]
    (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Φ.Ray)
    (hself : Φ.rayBoundarySelfIntersection hΦ r = -1) :
    ∃ (Ψ : Fan i) (_ : Ψ.IsRegular) (hΨc : Ψ.IsComplete) (σ : Ψ.cones)
      (_ : Nat.card (ToricRay σ.val) = 2) (h : Φ.IsSubdivision Ψ)
      (e : Φ.algebraicRealization ≅ (Ψ.distinguishedPointHom σ).ker.blowup),
      e.hom ≫ (Ψ.distinguishedPointHom σ).ker.blowupToBase = h.toFanHom.algebraicMap ∧
      (((Ψ.distinguishedPointHom σ).ker).comap
        (Ψ.distinguishedPointHom σ).ker.blowupToBase).comap e.hom = Φ.rayBoundaryIdeal hΦ r ∧
      (((Ψ.boundaryIdeal hΨc.nonempty_cones).comap
        (Ψ.distinguishedPointHom σ).ker.blowupToBase).radical).comap e.hom =
          Φ.boundaryIdeal hc.nonempty_cones := by
  obtain ⟨Ψ, hΨ, σ, hσ, hΨc, h, hr⟩ :=
    exists_star_subdivision_of_ray_self_intersection_neg_one b hΦ hc r hself
  subst Φ
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  obtain ⟨h₀, e, -, he, -⟩ := exists_iso_blowup_starSubdivisionAlong hΨ σ hN hσ
  let hsub := Ψ.starSubdivisionAlong_isSubdivision hΨ σ.property h₀
  have hr' : Ψ.starSubdivisionAlongRay hΨ σ.property h₀ = r := Subtype.ext (Subtype.ext hr)
  refine ⟨Ψ, hΨ, hΨc, σ, hσ, hsub, e, he, ?_,
    hsub.radical_comap_boundaryIdeal_of_iso hc.nonempty_cones hΨc.nonempty_cones _ e he⟩
  rw [← Scheme.IdealSheafData.comap_comp, he, ← hr']
  exact comap_ker_distinguishedPointHom_eq_rayBoundaryIdeal hΨ σ h₀ hN hσ

end TauCeti.Toric.Fan
