/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Boundary
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization

import QPainleve.Geometry.Toric.Cone.Coordinates
import QPainleve.Geometry.Toric.Fan.Boundary.Subdivision
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Contraction
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Generators
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

section Combinatorial

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N)

private theorem hirzebruch_star_at_corner (hΦ : Φ.IsRegular)
    {p r q : Φ.Ray} {σ τ : Φ.cones}
    (hp : p.primitiveGenerator = b 0) (hr : r.primitiveGenerator = b 1)
    (hq : q.primitiveGenerator = -b 0)
    (hpσ : p.toCone ≤ σ) (hrσ : r.toCone ≤ σ) (hrτ : r.toCone ≤ τ) (hqτ : q.toCone ≤ τ) :
    ∃ (hσ : Nat.card (ToricRay σ.val) = 2) (d : Basis (Fin 2) ℤ N),
      σ.val = hull ℝ (Set.range (i ∘ b)) ∧
      d 0 = b 0 ∧ d 1 = b 0 + b 1 ∧
      let F := Φ.starSubdivisionAlong hΦ σ.property
      let a := Φ.starSubdivisionAlongRay hΦ σ.property (ne_bot_of_card_toricRay_eq_two hσ)
      let hsub := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property
        (ne_bot_of_card_toricRay_eq_two hσ)
      a.primitiveGenerator = b 0 + b 1 ∧
      (∃ C : F.cones, a.toCone ≤ C ∧ (hsub.liftRay r).toCone ≤ C) ∧
      (∃ C : F.cones, (hsub.liftRay r).toCone ≤ C ∧ (hsub.liftRay q).toCone ≤ C) := by
  have hN : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
  have hpr : p ≠ r := fun h ↦ b.injective.ne (by decide : (0 : Fin 2) ≠ 1)
    (hp.symm.trans (h ▸ hr))
  have hσ := Φ.card_toricRay_eq_two_of_ray_ne_of_le hΦ hN hpr hpσ hrσ
  let hsub := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property
    (ne_bot_of_card_toricRay_eq_two hσ)
  let a := Φ.starSubdivisionAlongRay hΦ σ.property (ne_bot_of_card_toricRay_eq_two hσ)
  have hcone : σ.val = hull ℝ (Set.range (i ∘ b)) := by
    rw [Φ.cone_eq_sup_of_ray_ne_of_le hΦ hN hpr hpσ hrσ,
      p.toCone_eq_hull_primitiveGenerator, r.toCone_eq_hull_primitiveGenerator, hp, hr]
    rw [← Submodule.span_union]
    congr 1
    ext x
    simp [Fin.exists_fin_succ, eq_comm, or_comm]
  obtain ⟨d, hd₁, hd₀, -⟩ := Φ.exists_starSubdivisionAlong_basis hΦ σ.property b hcone 1
  have hd₀' : d 0 = b 0 := hd₀
  have hd₁' : d 1 = b 0 + b 1 := hd₁.trans (add_comm _ _)
  let hreg := (isRegular_iff.mp hΦ) _ σ.property
  have ha : a.primitiveGenerator = b 0 + b 1 :=
    primitiveGenerator_starSubdivisionAlongRay_of_basis hΦ σ b hcone _
  refine ⟨hσ, d, hcone, hd₀', hd₁', ha, ?_, ?_⟩
  · obtain ⟨c, hc₀, hc₁, hmem⟩ := Φ.exists_starSubdivisionAlong_basis hΦ σ.property b hcone 0
    refine ⟨⟨_, hmem⟩, (a.toCone_le_iff _).mpr ?_, ((hsub.liftRay r).toCone_le_iff _).mpr ?_⟩
    · have hc₀' : c 0 = b 0 + b 1 := hc₀
      rw [ha, ← hc₀']
      exact subset_hull (Set.mem_range_self 0)
    · have hc₁' : c 1 = b 1 := hc₁
      rw [hsub.primitiveGenerator_liftRay, hr, ← hc₁']
      exact subset_hull (Set.mem_range_self 1)
  · have hnot : ¬ σ ≤ τ := by
      intro h
      have hn := Φ.eq_of_le_fullCone hΦ hN hσ h
      have he := Φ.ray_eq_or_eq_of_le hreg hN hpr hpσ hrσ (hn ▸ hqτ)
      rcases he with h | h
      · have hzero := congrArg (b.coord 0) (hp.symm.trans (h.symm ▸ hq))
        simp at hzero
      · have hzero := congrArg (b.coord 1) (hr.symm.trans (h.symm ▸ hq))
        simp at hzero
    refine ⟨⟨τ.val, Φ.mem_starSubdivisionAlong_cones_of_not_le hΦ σ.property τ.property hnot⟩,
      ?_, ?_⟩
    · simpa only [← Subtype.coe_le_coe, IsSubdivision.liftRay_toCone] using hrτ
    · simpa only [← Subtype.coe_le_coe, IsSubdivision.liftRay_toCone] using hqτ

private theorem hirzebruch_elementary_transformation_rays {Ψ F : Fan i}
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (σ : Φ.cones) (τ : Ψ.cones)
    (hσ : Nat.card (ToricRay σ.val) = 2) (hτ : Nat.card (ToricRay τ.val) = 2)
    (hF : Φ.starSubdivisionAlong hΦ σ.property = F)
    (hG : Ψ.starSubdivisionAlong hΨ τ.property = F)
    (ha : (Φ.starSubdivisionAlongRay hΦ σ.property
      (ne_bot_of_card_toricRay_eq_two hσ)).primitiveGenerator = b 0 + b 1)
    (hr : (Ψ.starSubdivisionAlongRay hΨ τ.property
      (ne_bot_of_card_toricRay_eq_two hτ)).primitiveGenerator = b 1)
    (hremoved : hull ℝ {i (b 1)} ∉ Ψ.cones)
    (e : ℤ) (hrays : Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, e • b 0 - b 1}) :
    Set.range (Ray.primitiveGenerator (Phi := Ψ)) = {b 0, b 0 + b 1, -b 0, e • b 0 - b 1} := by
  have hΦs := range_primitiveGenerator_starSubdivisionAlong hΦ σ
    (ne_bot_of_card_toricRay_eq_two hσ)
  have hΨs := range_primitiveGenerator_starSubdivisionAlong hΨ τ
    (ne_bot_of_card_toricRay_eq_two hτ)
  rw [ha, hrays, hF] at hΦs
  rw [hr, hG] at hΨs
  have hnot : b 1 ∉ Set.range (Ray.primitiveGenerator (Phi := Ψ)) := by
    rintro ⟨v, hv⟩
    exact hremoved ((v.toCone_eq_hull_primitiveGenerator.trans (by rw [hv])) ▸ v.toCone.property)
  have hnot' : b 1 ∉ ({b 0, b 0 + b 1, -b 0, e • b 0 - b 1} : Set N) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h | h | h)
    · simpa using congrArg (b.coord 1) h
    · simpa using congrArg (b.coord 0) h
    · simpa using congrArg (b.coord 1) h
    · simpa using congrArg (b.coord 1) h
  have hinsert := hΨs.symm.trans hΦs
  rw [Set.insert_comm (b 0 + b 1) (b 0), Set.insert_comm (b 0 + b 1) (b 1),
    ← Set.insert_comm (b 1) (b 0)] at hinsert
  ext x
  by_cases hx : x = b 1
  · simp [hx, hnot, hnot']
  · simpa only [Set.mem_insert_iff, hx, false_or] using Set.ext_iff.mp hinsert x

/-- Blowing up the corner spanned by `b 0` and `b 1` and then contracting
the ray of `b 1` replaces the Hirzebruch parameter `e` by `e + 1` in the
basis `(b 0, b 0 + b 1)`. The same fan is the star subdivision at the
specified corner of the source and at the corner of the new fiber and the
opposite section of the target. The signed parameter lets either section be
the chosen section. -/
theorem exists_hirzebruch_toric_elementary_transformation (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (e : ℤ)
    (hrays : Set.range (Ray.primitiveGenerator (Phi := Φ)) =
      {b 0, b 1, -b 0, e • b 0 - b 1}) :
    ∃ (Ψ : Fan i) (hΨ : Ψ.IsRegular) (σ : Φ.cones) (τ : Ψ.cones)
      (hσ : Nat.card (ToricRay σ.val) = 2) (hτ : Nat.card (ToricRay τ.val) = 2)
      (d : Basis (Fin 2) ℤ N),
      Ψ.IsComplete ∧ σ.val = hull ℝ (Set.range (i ∘ b)) ∧
      d 0 = b 0 ∧ d 1 = b 0 + b 1 ∧
      Set.range (Ray.primitiveGenerator (Phi := Ψ)) = {d 0, d 1, -d 0, (e + 1) • d 0 - d 1} ∧
      Ψ.starSubdivisionAlong hΨ τ.property = Φ.starSubdivisionAlong hΦ σ.property ∧
      (Φ.starSubdivisionAlongRay hΦ σ.property
        (ne_bot_of_card_toricRay_eq_two hσ)).primitiveGenerator = b 0 + b 1 ∧
      (Ψ.starSubdivisionAlongRay hΨ τ.property
        (ne_bot_of_card_toricRay_eq_two hτ)).primitiveGenerator = b 1 ∧
      τ.val = hull ℝ {i (d 1), i (-d 0)} := by
  obtain ⟨rays, hgen⟩ := exists_rayEquiv_of_hirzebruch_ray_generators b e hrays
  obtain ⟨σ, hpσ, hrσ⟩ := exists_cone_of_hirzebruch_section_fiber b e rays hgen hΦ hc 0 0
  obtain ⟨τ, hqτ, hrτ⟩ := exists_cone_of_hirzebruch_section_fiber b e rays hgen hΦ hc 1 0
  let r := rays 1
  let q := rays 2
  have hp : (rays 0).primitiveGenerator = b 0 := congrFun hgen 0
  have hr : r.primitiveGenerator = b 1 := congrFun hgen 1
  have hq : q.primitiveGenerator = -b 0 := congrFun hgen 2
  obtain ⟨hσ, d, hcone, hd₀, hd₁, ha, hleft, hright⟩ :=
    hirzebruch_star_at_corner b hΦ hp hr hq hpσ hrσ hrτ hqτ
  let F := Φ.starSubdivisionAlong hΦ σ.property
  let hsub := Φ.starSubdivisionAlong_isSubdivision hΦ σ.property
    (ne_bot_of_card_toricRay_eq_two hσ)
  let a := Φ.starSubdivisionAlongRay hΦ σ.property (ne_bot_of_card_toricRay_eq_two hσ)
  let r' := hsub.liftRay r
  let q' := hsub.liftRay q
  have hr' : r'.primitiveGenerator = b 1 := (hsub.primitiveGenerator_liftRay r).trans hr
  have hq' : q'.primitiveGenerator = -b 0 := (hsub.primitiveGenerator_liftRay q).trans hq
  have hdet₁ : b.detDualEquiv a.primitiveGenerator r'.primitiveGenerator = 1 := by
    rw [ha, hr']
    simp only [map_add, LinearMap.add_apply, Basis.detDualEquiv_apply_basis_zero_one,
      Basis.detDualEquiv_self, add_zero]
  have hdet₂ : b.detDualEquiv r'.primitiveGenerator q'.primitiveGenerator = 1 := by
    rw [hr', hq', map_neg, b.detDualEquiv_swap (b 1) (b 0),
      b.detDualEquiv_apply_basis_zero_one, neg_neg]
  have hsum : a.primitiveGenerator + q'.primitiveGenerator = r'.primitiveGenerator := by
    rw [ha, hq', hr']
    abel
  obtain ⟨Ψ, hΨ, υ, hυ, hc', hstar, hRay, hremoved, hτcone⟩ :=
    F.exists_star_subdivision_of_ray_eq_sum b (Φ.isRegular_starSubdivisionAlong hΦ σ.property)
      (hsub.isComplete_iff.mpr hc) ⟨hdet₁, hleft⟩ ⟨hdet₂, hright⟩ hsum
  have hrHull : r'.toCone.val = hull ℝ {i (b 1)} := by
    rw [r'.toCone_eq_hull_primitiveGenerator, hr']
  let u := Ψ.starSubdivisionAlongRay hΨ υ.property (ne_bot_of_card_toricRay_eq_two hυ)
  have hu : u.primitiveGenerator = b 1 := by
    apply u.primitiveGenerator_eq_of_mem_of_isPrimitive _ (b.isPrimitive 1)
    rw [hRay, hrHull]
    exact subset_hull (Set.mem_singleton _)
  refine ⟨Ψ, hΨ, σ, υ, hσ, hυ, d, hc', hcone, hd₀, hd₁, ?_, hstar, ha, hu, ?_⟩
  · rw [hirzebruch_elementary_transformation_rays b hΦ hΨ σ υ hσ hυ rfl hstar ha hu
      (hrHull ▸ hremoved) e hrays, hd₀, hd₁, add_zsmul, one_zsmul]
    congr 4
    abel
  · rw [hτcone, a.toCone_eq_hull_primitiveGenerator, q'.toCone_eq_hull_primitiveGenerator,
      ha, hq', hd₀, hd₁, ← Submodule.span_union, Set.singleton_union]

end Combinatorial

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
