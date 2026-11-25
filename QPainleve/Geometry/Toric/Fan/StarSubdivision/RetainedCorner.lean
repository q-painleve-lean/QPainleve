/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.DistinguishedPoint
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Global

import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Retained corner centers of a toric pivot

The point of a retained corner lifts to a distinguished point on the common
star subdivision. Its image is a corner of the new fan. The first center over
this image is either the transported center or the first reverse center. This
comparison carries previously marked corners through the next toric pivot.
The elementary link is the one in [Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module TauCeti.Toric

namespace QPainleve

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ F : Fan i} {n : ℕ}

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedPointHom _ σ)
local notation "π[" s "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom s)
local notation "node[" Δ "," σ "]" =>
  Fan.distinguishedPointHom Δ σ (IsLocalRing.closedPoint ℂ)

/-- A retained first center over a toric corner different from the pivot
projects to a toric corner after the elementary link. The first index over
the image is the transported index or the reverse pivot. -/
theorem retained_corner_of_toric_link
    (hN : finrank ℤ N = 2) (hΦ : Φ.IsRegular) (hF : F.IsRegular) (hΨ : Ψ.IsRegular)
    (hcΨ : Ψ.IsComplete) (hstar : Φ.IsTwoRayStarSubdivision F)
    {σ : Φ.cones} {τ : Ψ.cones} (t : F.IsSubdivision Ψ)
    (v : X[F] ≅ (I[σ]).blowup) (w : X[F] ≅ (I[τ]).blowup)
    (hv : v.hom ≫ (I[σ]).blowupToBase = π[hstar.isSubdivision])
    (hw : w.hom ≫ (I[τ]).blowupToBase = π[t])
    {sourceCenters : Fin n → X[Φ]} {targetCenters : Fin (1 + n) → X[Ψ]}
    (hhead : targetCenters (Fin.castAdd n (0 : Fin 1)) = node[Ψ,τ])
    (hretained : ∀ k : Fin n, ∃ z : X[F],
      π[hstar.isSubdivision] z = sourceCenters k ∧ π[t] z = targetCenters (k.natAdd 1))
    (l : Fin n) {ω : Φ.cones} (hω : Nat.card (ToricRay ω.val) = 2)
    (hl : sourceCenters l = node[Φ,ω]) (hne : node[Φ,ω] ≠ node[Φ,σ])
    (hfirst : ∀ k < l, sourceCenters k ≠ sourceCenters l) :
    ∃ ω' : Ψ.cones, Nat.card (ToricRay ω'.val) = 2 ∧
      targetCenters (l.natAdd 1) = node[Ψ,ω'] ∧
      ∃ k : Fin (1 + n), (k = Fin.castAdd n (0 : Fin 1) ∨ k = l.natAdd 1) ∧
        targetCenters k = node[Ψ,ω'] ∧ ∀ a < k, targetCenters a ≠ targetCenters k := by
  let s := hstar.isSubdivision
  obtain ⟨υ, hυ, hsυ⟩ := hstar.exists_lift_distinguishedPointHom hN ω hω
  let z := node[F,υ]
  have hsrc : π[s] z = node[Φ,ω] :=
    congrArg (fun f : Spec (.of ℂ) ⟶ X[Φ] ↦ f (IsLocalRing.closedPoint ℂ)) hsυ
  let least : Ψ.cones := ⟨t.toFanHom.leastCone υ.property, t.toFanHom.leastCone_mem υ.property⟩
  obtain ⟨ω', hleast, hω'⟩ := Ψ.exists_le_cone_of_card_toricRay_eq_two hΨ hcΨ hN least
  have hcomp := t.distinguishedPointHom_comp_algebraicMap_of_le_of_card_toricRay_eq_two hF hN hυ
    ((t.le_leastCone υ.property).trans hleast)
  have htgt : π[t] z = node[Ψ,ω'] :=
    congrArg (fun f : Spec (.of ℂ) ⟶ X[Ψ] ↦ f (IsLocalRing.closedPoint ℂ)) hcomp
  have hoff : π[s] z ∈ π[s].isoLocus := by
    have hnon : π[s] z ∉ π[s].centre := by
      rw [hsrc, Φ.centre_eq_singleton_distinguishedPoint_of_blowup hΦ hN σ _ v hv]
      exact fun h ↦ hne (Set.mem_singleton_iff.mp h)
    simpa only [Scheme.Hom.centre_def, Set.mem_compl_iff, not_not, SetLike.mem_coe] using hnon
  refine ⟨ω', hω', ?_⟩
  by_cases he : node[Ψ,ω'] = node[Ψ,τ]
  · obtain ⟨u, hu, hu'⟩ := hretained l
    have hproj := hu.trans (hl.trans hsrc.symm)
    have hz := (π[s]).injOn_preimage_isoLocus (by rwa [Set.mem_preimage, hproj]) hoff hproj
    have himage := hu'.symm.trans ((congrArg (π[t]) hz).trans htgt)
    refine ⟨himage, _, Or.inl rfl, hhead.trans he.symm, fun a ha ↦ ?_⟩
    exact (Nat.not_lt_zero _ ha).elim
  · have htarget : π[t] z ∈ π[t].isoLocus := by
      have hnon : π[t] z ∉ π[t].centre := by
        rw [htgt, Ψ.centre_eq_singleton_distinguishedPoint_of_blowup hΨ hN τ _ w hw]
        exact fun h ↦ he (Set.mem_singleton_iff.mp h)
      simpa only [Scheme.Hom.centre_def, Set.mem_compl_iff, not_not, SetLike.mem_coe] using hnon
    have hheadOff : targetCenters (Fin.castAdd n (0 : Fin 1)) ∉ π[t].isoLocus := by
      rw [hhead]
      exact Ψ.notMem_isoLocus_distinguishedPoint_of_blowup hΨ hN τ _ w hw
    obtain ⟨himage, hf⟩ := (π[s]).first_occurrence_of_projected_points (π[t])
      hheadOff hretained hoff htarget l (hl.trans hsrc.symm) (by simpa only [hsrc, hl] using hfirst)
    exact ⟨himage.trans htgt, _, Or.inr rfl, himage.trans htgt,
      fun a ha heq ↦ hf a ha (heq.trans himage)⟩

end QPainleve
