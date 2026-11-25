/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.SelfIntersection
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Factorization
public import QPainleve.Geometry.Toric.Fan.Boundary.Ideal
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
public import QPainleve.LinearAlgebra.Determinant.Dual

import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
import QPainleve.Geometry.Toric.Cone.Coordinates
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Construction
import QPainleve.Geometry.Toric.Fan.Hirzebruch.Corner
import QPainleve.Geometry.Toric.Fan.Picard.Rank
import QPainleve.Geometry.Toric.Fan.Smooth
import QPainleve.Geometry.Toric.Fan.StarSubdivision.FullCones
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# The four-corner subdivision of the quadric fan

Subdividing the four quadrants of the quadric fan inserts the diagonal rays.
The resulting positive cyclic numbering starts at the first coordinate ray.
The four diagonal rays in this numbering are the ones carrying the internal
centers of the four-vertex doubled-square seed.
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.FourVertex

local notation "L" => (Fin 2 → ℤ)
local notation "i₂" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
local notation "b₂" => Pi.basisFun ℤ (Fin 2)

/-- The primitive generators of the subdivided quadric fan in positive cyclic
order, starting at the first coordinate ray. -/
def octagonGenerator (j : ZMod 8) : L :=
  ![![1, 0], ![1, 1], ![0, 1], ![-1, 1], ![-1, 0], ![-1, -1], ![0, -1], ![1, -1]]
    ((ZMod.finEquiv 8).symm j)

/-- The cyclic ray coordinates, starting at `(1, 0)`. -/
theorem octagonGenerator_apply (j : ZMod 8) :
    octagonGenerator j =
      ![![1, 0], ![1, 1], ![0, 1], ![-1, 1], ![-1, 0], ![-1, -1], ![0, -1], ![1, -1]]
        ((ZMod.finEquiv 8).symm j) := (rfl)

private def quadrantSign (k : Fin 4) : Fin 2 → ℤˣ :=
  ![![1, 1], ![-1, 1], ![-1, -1], ![1, -1]] k

private noncomputable def quadrantBasis (k : Fin 4) : Basis (Fin 2) ℤ L :=
  Basis.unitsSMul b₂ (quadrantSign k)

private theorem quadrantBasis_apply (k : Fin 4) (a : Fin 2) :
    quadrantBasis k a = Pi.single a (quadrantSign k a : ℤ) := by
  ext j
  by_cases h : a = j
  · subst j
    simp [quadrantBasis, Basis.unitsSMul_apply, Pi.basisFun_apply, Units.smul_def]
  · simp [quadrantBasis, Basis.unitsSMul_apply, Pi.basisFun_apply, Ne.symm h]

local notation "σ[" k "]" => hull ℝ (Set.range (fun j : Fin 2 ↦ i₂ (quadrantBasis k j)))

variable {Φ : Fan i₂}

private theorem quadrant_mem (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b₂ 0, b₂ 1, -b₂ 0, (0 : ℤ) • b₂ 0 - b₂ 1])
    (k : Fin 4) : σ[k] ∈ Φ.cones := by
  have c := Φ.hirzebruch_chart_corners b₂ 0 r hr hΦ hc
  simp only [zero_smul, zero_sub] at c
  have h : Set.range (fun j : Fin 2 ↦ i₂ (quadrantBasis k j)) =
      {i₂ (quadrantBasis k 0), i₂ (quadrantBasis k 1)} := by
    ext x
    simp [Fin.exists_fin_succ, eq_comm]
  rw [h]
  fin_cases k
  · simpa [quadrantBasis, Basis.unitsSMul_apply, quadrantSign] using c 0 0
  · simpa [quadrantBasis, Basis.unitsSMul_apply, quadrantSign, Units.smul_def] using c 1 0
  · simpa [quadrantBasis, Basis.unitsSMul_apply, quadrantSign, Units.smul_def] using c 1 1
  · simpa [quadrantBasis, Basis.unitsSMul_apply, quadrantSign, Units.smul_def] using c 0 1

private theorem quadrant_cone_injective (hΦ : Φ.IsRegular) (hmem : ∀ k, σ[k] ∈ Φ.cones) :
    Function.Injective (fun k : Fin 4 ↦ σ[k]) := by
  intro j k he
  let hreg := Fan.isRegular_iff.mp hΦ _ (hmem j)
  obtain ⟨r, hr⟩ := hreg.exists_rayEquiv_of_basis Φ.lattice (quadrantBasis j) rfl
  obtain ⟨s, hs⟩ := hreg.exists_rayEquiv_of_basis Φ.lattice (quadrantBasis k) he
  have hsum : quadrantBasis j 0 + quadrantBasis j 1 = quadrantBasis k 0 + quadrantBasis k 1 :=
    (hreg.sum_primitiveGenerator_allRays Φ.lattice _ r hr).symm.trans
      (hreg.sum_primitiveGenerator_allRays Φ.lattice _ s hs)
  have hinj : Function.Injective (fun k : Fin 4 ↦
      (Pi.single (0 : Fin 2) (quadrantSign k 0 : ℤ) +
        Pi.single (1 : Fin 2) (quadrantSign k 1 : ℤ) : L)) := by decide
  exact hinj (by simpa only [quadrantBasis_apply] using hsum)

private theorem octagonGenerator_injective : Function.Injective octagonGenerator := by
  decide

private theorem exists_quadrantChart (j : ZMod 8) :
    ∃ (k : Fin 4) (a : Fin 2),
      let u := quadrantBasis k 0 + quadrantBasis k 1
      let v := quadrantBasis k a
      (octagonGenerator j = u ∧ octagonGenerator (j + 1) = v) ∨
      (octagonGenerator j = v ∧ octagonGenerator (j + 1) = u) := by
  simp only [quadrantBasis_apply]
  revert j
  decide

private theorem octagonGenerator_det (j : ZMod 8) :
    Basis.detDualEquiv b₂ (octagonGenerator j) (octagonGenerator (j + 1)) = 1 := by
  simp only [Basis.detDualEquiv_apply, Basis.det_apply, Matrix.det_fin_two,
    Basis.toMatrix_apply, Pi.basisFun_repr, Matrix.cons_val_zero, Matrix.cons_val_one]
  revert j
  decide

private theorem octagonGenerator_range (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b₂ 0, b₂ 1, -b₂ 0, (0 : ℤ) • b₂ 0 - b₂ 1]) :
    Set.range octagonGenerator = Set.range (Fan.Ray.primitiveGenerator (Phi := Φ)) ∪
      Set.range (fun k : Fin 4 ↦ quadrantBasis k 0 + quadrantBasis k 1) := by
  rw [← r.surjective.range_comp, Function.comp_def, hr]
  have hb : (![b₂ 0, b₂ 1, -b₂ 0, (0 : ℤ) • b₂ 0 - b₂ 1] : Fin 4 → L) =
      ![![1, 0], ![0, 1], ![-1, 0], ![0, -1]] := by
    ext j a
    fin_cases j <;> fin_cases a <;> simp [Pi.basisFun_apply]
  rw [hb]
  simp only [quadrantBasis_apply]
  apply Set.Subset.antisymm
  · rintro _ ⟨j, rfl⟩
    exact (by decide : ∀ j : ZMod 8, (∃ k : Fin 4,
      (![![1, 0], ![0, 1], ![-1, 0], ![0, -1]] : Fin 4 → L) k = octagonGenerator j) ∨
      (∃ k : Fin 4, Pi.single 0 (quadrantSign k 0 : ℤ) + Pi.single 1 (quadrantSign k 1 : ℤ) =
        octagonGenerator j)) j
  · rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact (by decide : ∀ k : Fin 4, ∃ j : ZMod 8,
        octagonGenerator j = (![![1, 0], ![0, 1], ![-1, 0], ![0, -1]] : Fin 4 → L) k) k
    · exact (by decide : ∀ k : Fin 4, ∃ j : ZMod 8,
        octagonGenerator j = Pi.single 0 (quadrantSign k 0 : ℤ) +
          Pi.single 1 (quadrantSign k 1 : ℤ)) k

/-- Subdivision of the four corners of the quadric fan gives a complete regular
fan with the indicated eight rays. Consecutive rays share a cone and have
determinant one in the standard orientation. -/
theorem exists_four_vertex_octagon_fan (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (r : Fin 4 ≃ Φ.Ray)
    (hr : (fun j ↦ (r j).primitiveGenerator) = ![b₂ 0, b₂ 1, -b₂ 0, (0 : ℤ) • b₂ 0 - b₂ 1]) :
    ∃ (Ψ : Fan i₂) (_ : Ψ.IsRegular) (_ : Ψ.IsComplete) (v : ZMod 8 ≃ Ψ.Ray),
      Relation.ReflTransGen Fan.IsTwoRayStarSubdivision Φ Ψ ∧
      (∀ j, (v j).primitiveGenerator = octagonGenerator j) ∧
      ∀ j, Basis.detDualEquiv b₂ (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ := by
  have hmem := quadrant_mem hΦ hc r hr
  let B := List.ofFn quadrantBasis
  have hB : (B.map (fun (b : Basis (Fin 2) ℤ L) ↦ hull ℝ (Set.range (i₂ ∘ ⇑b)))).Nodup := by
    rw [List.map_ofFn, List.nodup_ofFn]
    exact quadrant_cone_injective hΦ hmem
  have hb : ∀ d ∈ B, hull ℝ (Set.range (i₂ ∘ ⇑d)) ∈ Φ.cones := by
    intro d hd
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hd
    exact hmem k
  obtain ⟨Ψ, hΨ, hpath, hrays, hcharts, -⟩ :=
    Φ.exists_starSubdivisionAlong_basis_list hΦ B hB hb
  have hcom := (Fan.isSubdivision_of_starSubdivision_chain hpath).isComplete_iff.mpr hc
  have hrange : Set.range octagonGenerator = Set.range (Fan.Ray.primitiveGenerator (Phi := Ψ)) := by
    rw [hrays, octagonGenerator_range r hr]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq, B, List.mem_ofFn]
    exact ⟨fun ⟨k, hk⟩ ↦ ⟨quadrantBasis k, ⟨k, rfl⟩, hk⟩,
      fun ⟨d, ⟨k, hk⟩, hd⟩ ↦ ⟨k, hk ▸ hd⟩⟩
  let e := Equiv.ofInjective _ octagonGenerator_injective
  let f := Equiv.ofInjective _ (Fan.Ray.primitiveGenerator_injective (Φ := Ψ))
  let v := e.trans ((Set.equivOfEq hrange).trans f.symm)
  have hv (j) : (v j).primitiveGenerator = octagonGenerator j :=
    congrArg Subtype.val (f.apply_symm_apply (Set.equivOfEq hrange (e j)))
  refine ⟨Ψ, hΨ, hcom, v, hpath, hv, fun j ↦ ⟨?_, ?_⟩⟩
  · simpa only [hv] using octagonGenerator_det j
  · obtain ⟨k, a, h⟩ := exists_quadrantChart j
    refine ⟨⟨_, hcharts (quadrantBasis k) (List.mem_ofFn.mpr ⟨k, rfl⟩) a⟩, ?_, ?_⟩ <;>
      rw [Fan.Ray.toCone_le_iff, hv] <;>
      apply subset_hull <;>
      rcases h with h | h <;>
      simp [h.1, h.2]

private theorem octagonGenerator_ne_zero (j : ZMod 8) : octagonGenerator j ≠ 0 := by
  revert j
  decide

private theorem octagonGenerator_relation (j : ZMod 8) :
    octagonGenerator (j - 1) +
      (if j.val % 2 = 0 then (-2 : ℤ) else -1) • octagonGenerator j +
        octagonGenerator (j + 1) = 0 := by
  revert j
  decide

/-- The coordinate rays of the octagon have self-intersection `-2` and its
diagonal rays have self-intersection `-1`. -/
theorem rayBoundarySelfIntersection_eq_of_octagon (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (v : ZMod 8 ≃ Φ.Ray) (hv : ∀ j, (v j).primitiveGenerator = octagonGenerator j)
    (hnext : ∀ j, ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
    (j : ZMod 8) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    Φ.rayBoundarySelfIntersection hΦ (v j) = if j.val % 2 = 0 then -2 else -1 := by
  let : Φ.algebraicRealization.IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b₂
  have hpair (a : ZMod 8) :
      Basis.detDualEquiv b₂ (v a).primitiveGenerator (v (a + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, (v a).toCone ≤ σ ∧ (v (a + 1)).toCone ≤ σ :=
    ⟨by simpa only [hv] using octagonGenerator_det a, hnext a⟩
  have hprev := hpair (j - 1)
  rw [sub_add_cancel] at hprev
  have h := Φ.primitiveGenerator_add_selfIntersection_smul_add_eq_zero b₂ hΦ hc hprev (hpair j)
  simp only [hv] at h
  exact (smul_left_injective ℤ (octagonGenerator_ne_zero j))
    (add_left_cancel (add_right_cancel (h.trans (octagonGenerator_relation j).symm)))

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Pic[" X "]" => Additive (LineBundleClass X)

private theorem octagon_tower_length {Ψ : Fan i₂}
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
    (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (v : ZMod 8 ≃ Ψ.Ray)
    {n : ℕ} {Y : Scheme} {T : BlowupTower Φ.algebraicRealization n Y}
    (hT : IsClosedPointTower Φ.algebraicRealization T) (e : Ψ.algebraicRealization ≅ Y) :
    n = 4 := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : IsIntegral Φ.algebraicRealization := inferInstance
  let : IsNoetherian Φ.algebraicRealization := inferInstance
  have h₂ : finrank ℤ L = 2 := (finrank_eq_card_basis b₂).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) := by
    rw [Fan.algebraicRealization_over]
    simpa only [h₂] using Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Module.Finite ℤ Pic[Φ.algebraicRealization] :=
    Module.Finite.of_surjective (Φ.rayDivisorToPicard hΦ).toIntLinearMap
      (Φ.rayDivisorToPicard_surjective hΦ)
  have h₄ := Φ.finrank_picard_add_finrank_eq_natCard_ray hΦ hc
  have h₈ := Ψ.finrank_picard_add_finrank_eq_natCard_ray hΨ hcΨ
  rw [h₂, ← Nat.card_congr r, Nat.card_fin] at h₄
  rw [h₂, ← Nat.card_congr v, Nat.card_zmod] at h₈
  have hY := finrank_picard ℂ hT
  have he := (LineBundleClass.pullbackEquiv e).toAdditive.toIntLinearEquiv.finrank_eq
  omega

/-- The octagon realizes a four-step blowup tower of nodes of the quadric
boundary. The comparison identifies the projection and the reduced total
boundary, with rays numbered by the explicit positive octagon. -/
theorem exists_four_vertex_octagon_blowup :
    ∃ (Φ : Fan i₂) (_ : Φ.IsRegular) (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray),
      (fun j ↦ (r j).primitiveGenerator) = ![b₂ 0, b₂ 1, -b₂ 0, (0 : ℤ) • b₂ 0 - b₂ 1] ∧
      ∃ (Ψ : Fan i₂) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete) (v : ZMod 8 ≃ Ψ.Ray)
        (h : Ψ.IsSubdivision Φ) (Y : Scheme) (T : BlowupTower Φ.algebraicRealization 4 Y)
        (e : Ψ.algebraicRealization ≅ Y),
        IsNodalBoundaryTower (Φ.boundaryIdeal hc.nonempty_cones) Φ.algebraicRealizationStructureMap
          (𝟙 _) T ∧
        e.hom ≫ T.toBase = h.toFanHom.algebraicMap ∧
        ((Φ.boundaryIdeal hc.nonempty_cones).comap T.toBase).radical.comap e.hom =
          Ψ.boundaryIdeal hcΨ.nonempty_cones ∧
        (∀ j, (v j).primitiveGenerator = octagonGenerator j) ∧
        (∀ j, Basis.detDualEquiv b₂ (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
          ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ) ∧
        ∀ j, letI : Nonempty Ψ.cones := hcΨ.nonempty_cones
          Ψ.rayBoundarySelfIntersection hΨ (v j) = if j.val % 2 = 0 then -2 else -1 := by
  obtain ⟨Φ, ⟨hΦ, hc, hrays⟩, -⟩ :=
    Fan.existsUnique_hirzebruch_fan b₂ (isIntegralLattice_intCast 2) 0
  obtain ⟨r, hr⟩ := Fan.exists_rayEquiv_of_hirzebruch_ray_generators b₂ 0 hrays
  obtain ⟨Ψ, hΨ, hcΨ, v, hpath, hv, hnext⟩ := exists_four_vertex_octagon_fan hΦ hc r hr
  let h := Fan.isSubdivision_of_starSubdivision_chain hpath
  have h₂ : finrank ℤ L = 2 := (finrank_eq_card_basis b₂).trans (Fintype.card_fin 2)
  obtain ⟨n, Y, T, e, hT, he, hboundary, -⟩ :=
    h.exists_toric_subdivision_blowup_tower hΦ hΨ hc.nonempty_cones h₂
  have hn := octagon_tower_length hΦ hc r hΨ hcΨ v hT.isClosedPointTower e
  subst n
  refine ⟨Φ, hΦ, hc, r, hr, Ψ, hΨ, hcΨ, v, h, Y, T, e, hT, he, hboundary, hv, hnext, ?_⟩
  exact rayBoundarySelfIntersection_eq_of_octagon hΨ hcΨ v hv (fun j ↦ (hnext j).2)

end QPainleve.FourVertex
