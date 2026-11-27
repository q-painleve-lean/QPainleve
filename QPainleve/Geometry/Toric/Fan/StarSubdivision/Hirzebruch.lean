/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization

import QPainleve.Geometry.Toric.Cone.Coordinates
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.StarSubdivision.TwoDimensional
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Toric elementary transformations of Hirzebruch surfaces

Blow up the corner where a toric fiber meets a section and contract the strict
transform of that fiber. The common fan is a star subdivision of each end.
With signed parameter `e` for the chosen section of square `-e`, the new
parameter is `e + 1`. The two toric projections restrict to the identity on
the common dense torus.

This is the toric elementary transformation in Lutz's proof of Proposition 8.11
in [the appendix to Hacking and Keating](https://arxiv.org/abs/2005.05010v3).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TopologicalSpace
open TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N)

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedPointHom _ σ)
local notation "rays[" Δ "]" => Set.range (Ray.primitiveGenerator (Phi := Δ))

/-- A toric elementary transformation at a Hirzebruch corner is represented by
two ordinary point blowups. The projection to the source blows up the fixed
point of the cone spanned by `b 0` and `b 1`. The projection to the target
contracts the strict transform of the fiber of ray `b 1`. Both projections
are single star subdivisions at two-ray cones and pull back the reduced
boundary to the common reduced boundary after taking radicals. The reverse center is the
corner on the new fiber and the opposite section. -/
theorem exists_blowup_span_hirzebruch_toric_elementary_transformation
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (e : ℤ)
    (hrays : rays[Φ] = {b 0, b 1, -b 0, e • b 0 - b 1}) :
    ∃ (Ψ F : Fan i) (_ : Ψ.IsRegular) (hF : F.IsRegular)
      (hc' : Ψ.IsComplete) (hcF : F.IsComplete) (d : Basis (Fin 2) ℤ N)
      (σ : Φ.cones) (τ : Ψ.cones) (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
      (g : X[F] ≅ (I[σ]).blowup) (g' : X[F] ≅ (I[τ]).blowup) (a : F.Ray) (r : Φ.Ray),
      σ.val = hull ℝ (Set.range (i ∘ b)) ∧ d 0 = b 0 ∧ d 1 = b 0 + b 1 ∧
      rays[Ψ] = {d 0, d 1, -d 0, (e + 1) • d 0 - d 1} ∧
      a.primitiveGenerator = b 0 + b 1 ∧ r.primitiveGenerator = b 1 ∧
      g.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap ∧
      g'.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap ∧
      (I[σ]).comap s.toFanHom.algebraicMap = F.rayBoundaryIdeal hF a ∧
      (I[τ]).comap t.toFanHom.algebraicMap = F.rayBoundaryIdeal hF (s.liftRay r) ∧
      ((I[σ]).blowupMap (Φ.rayBoundaryIdeal hΦ r).subschemeι).ker.comap g.hom =
        F.rayBoundaryIdeal hF (s.liftRay r) ∧
      ((Φ.boundaryIdeal hc.nonempty_cones).comap s.toFanHom.algebraicMap).radical =
        F.boundaryIdeal hcF.nonempty_cones ∧
      ((Ψ.boundaryIdeal hc'.nonempty_cones).comap t.toFanHom.algebraicMap).radical =
        F.boundaryIdeal hcF.nonempty_cones ∧
      Φ.IsTwoRayStarSubdivision F ∧ Ψ.IsTwoRayStarSubdivision F ∧
      τ.val = hull ℝ {i (d 1), i (-d 0)} := by
  obtain ⟨Ψ, hΨ, σ, τ, hσ, hτ, d, hc', hcone, hd₀, hd₁, hrays', hstar, ha, hr, hτcone⟩ :=
    exists_hirzebruch_toric_elementary_transformation b hΦ hc e hrays
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  let F := Φ.starSubdivisionAlong hΦ σ.property
  obtain ⟨h₀, g, -, hg, -⟩ := Φ.exists_iso_blowup_starSubdivisionAlong hΦ σ hN hσ
  let s := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property h₀
  let a := Φ.starSubdivisionAlongRay hΦ σ.property h₀
  have hF := Φ.isRegular_starSubdivisionAlong hΦ σ.property
  have hcF := s.isComplete_iff.mpr hc
  let TargetComparison (G : Fan i) : Prop :=
    ∃ (hG : G.IsRegular) (t : G.IsSubdivision Ψ) (g' : X[G] ≅ (I[τ]).blowup) (r' : G.Ray),
      r'.primitiveGenerator = b 1 ∧ g'.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap ∧
      (I[τ]).comap t.toFanHom.algebraicMap = G.rayBoundaryIdeal hG r'
  have htarget : TargetComparison F := by
    -- Transport the entire target-side comparison along equality of the common fans.
    rw [show F = Ψ.starSubdivisionAlong hΨ τ.property from hstar.symm]
    obtain ⟨h₀', g', -, hg', -⟩ := Ψ.exists_iso_blowup_starSubdivisionAlong hΨ τ hN hτ
    exact ⟨_, _, g', _, hr, hg',
      Ψ.comap_ker_distinguishedPointHom_eq_rayBoundaryIdeal hΨ τ h₀' hN hτ⟩
  obtain ⟨_, t, g', r', hr', hg', htarget⟩ := htarget
  obtain ⟨r, hgen⟩ : b 1 ∈ rays[Φ] := by rw [hrays]; simp
  have hLift : s.liftRay r = r' := Ray.primitiveGenerator_injective
    ((s.primitiveGenerator_liftRay r).trans (hgen.trans hr'.symm))
  have hsource := Φ.comap_ker_distinguishedPointHom_eq_rayBoundaryIdeal hΦ σ h₀ hN hσ
  have hnot : (Φ.rayBoundaryPoint hΦ r).val ∉ ((I[σ]).support : Set X[Φ]) := by
    rw [← s.algebraicMap_rayBoundaryPoint_liftRay hF hΦ r, ← Set.mem_preimage,
      ← Closeds.coe_preimage _ s.toFanHom.algebraicMap.continuous,
      ← support_comap, hsource, F.coe_support_rayBoundaryIdeal]
    intro hm
    have he := F.rayBoundaryPoint_injective hF
      (CodimensionOnePoint.eq_of_specializes (specializes_iff_mem_closure.mpr hm))
    have hn := congrArg (b.coord 0) (ha.symm.trans
      ((congrArg Ray.primitiveGenerator he).trans (hLift ▸ hr')))
    simp at hn
  refine ⟨Ψ, F, hΨ, hF, hc', hcF, d, σ, τ, s, t, g, g', a, r,
    hcone, hd₀, hd₁, hrays', ha, hgen, hg, hg', hsource,
    hLift.symm ▸ htarget, s.comap_ker_blowupMap_rayBoundaryIdeal hF hΦ g hg r hnot,
    s.radical_comap_boundaryIdeal hcF.nonempty_cones hc.nonempty_cones,
    t.radical_comap_boundaryIdeal hcF.nonempty_cones hc'.nonempty_cones,
    .along hΦ σ hσ, ?_, hτcone⟩
  dsimp only [F]
  rw [← hstar]
  exact .along hΨ τ hτ

end TauCeti.Toric.Fan
