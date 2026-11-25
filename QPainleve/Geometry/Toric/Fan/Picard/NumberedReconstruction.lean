/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.CycleAction
public import QPainleve.Geometry.Toric.Fan.Boundary.Numbering
public import QPainleve.Geometry.Toric.Fan.Picard.Reconstruction

import QPainleve.Geometry.Toric.Fan.Equiv

/-!
# Toric reconstruction with prescribed boundary numberings

Matching the strict boundary classes in prescribed nodal cycle numberings
determines the map between the toric bases, including its action on the ordered
branches. Matching the total exceptional classes then describes the isometry on
all classes in blowup coordinates. This is the comparison of the contracted models
in [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
proof of Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry
open LineBundleClass
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  [Φ.algebraicRealization.IsProjectiveOver ℂ] [Ψ.algebraicRealization.IsProjectiveOver ℂ]

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "C[" A "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal A inferInstance)
local notation "s(" A ")" => (Fan.algebraicRealization A ↘ S)
local notation "Pic(" X ")" => Additive (LineBundleClass X)
local notation "B(" X ")" => Chow.intersectionBilinForm ℂ X
local notation "rankTwo(" b ")" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

variable [PrestableFamily (C[Φ] ↘ S)] [PrestableFamily (C[Ψ] ↘ S)]
  {ι ι' : Type*} {p : ι → (C[Φ] ↘ S).smoothLocus} {q : ι' → (C[Ψ] ↘ S).smoothLocus}
  {m n : ℕ} [NeZero m] {Y W : Scheme}
  {T : BlowupTower Φ.algebraicRealization n Y} {U : BlowupTower Ψ.algebraicRealization n W}

variable (Φ) in
/-- A Picard isometry matching the ordered total exceptional classes and the strict
transforms of the numbered boundary components determines a unique fan equivalence.
It matches the actual ordered branches on the toric bases and gives the pullback on
the base summand of the given isometry, with every exceptional coefficient fixed. -/
theorem existsUnique_fanEquiv_of_numbered_strictRayBoundaryClasses
    (b : Basis (Fin 2) ℤ N) (b' : Basis (Fin 2) ℤ N')
    (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete) (hc' : Ψ.IsComplete)
    (A : NodalCycleNumbering p m) (A' : NodalCycleNumbering q m)
    (hT : IsClosedPointTower Φ.algebraicRealization T)
    (hU : IsClosedPointTower Ψ.algebraicRealization U)
    (e :
      let : SmoothOfRelativeDimension 2 s(Φ) :=
        rankTwo(b) ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
      let : SmoothOfRelativeDimension 2 s(Ψ) :=
        rankTwo(b') ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
      let : IsNoetherian Φ.algebraicRealization := isNoetherian_of_finiteType s(Φ)
      let : IsNoetherian Ψ.algebraicRealization := isNoetherian_of_finiteType s(Ψ)
      let : Y.Over S := ⟨T.toBase ≫ s(Φ)⟩
      let : W.Over S := ⟨U.toBase ≫ s(Ψ)⟩
      let : Y.IsProjectiveOver ℂ := T.isProjectiveOver ℂ
      let : W.IsProjectiveOver ℂ := U.isProjectiveOver ℂ
      let : IsIntegral Y := hT.isIntegral s(Φ)
      let : IsIntegral W := hU.isIntegral s(Ψ)
      let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s(Φ)
      let : SmoothOfRelativeDimension 2 (W ↘ S) := hU.smoothOfRelativeDimension s(Ψ)
      B(W).IsometryEquiv B(Y))
    (he : ∀ j, e (Additive.ofMul (U.exceptionalClass j)) = Additive.ofMul (T.exceptionalClass j))
    (hD : ∀ j,
      e (strictRayBoundaryClass hΨ rankTwo(b') U hU (Ψ.rayEquivOfNodalCycleNumbering hΨ A' j)) =
        strictRayBoundaryClass hΦ rankTwo(b) T hT (Φ.rayEquivOfNodalCycleNumbering hΦ A j)) :
    ∃! f : FanEquiv Φ Ψ,
      (f.boundaryIso hΦ₀ hΨ₀).boundaryCycleAction A A' = 1 ∧
      ∀ (a : Pic(Ψ.algebraicRealization)) (t : Fin n → ℤ),
        e (U.picardHom (a, t)) =
          T.picardHom (Additive.ofMul (pullback f.toFanHom.algebraicMap a.toMul), t) := by
  let u := Φ.rayEquivOfNodalCycleNumbering hΦ A
  let v := Ψ.rayEquivOfNodalCycleNumbering hΨ A'
  obtain ⟨d, -, hu, hnodes⟩ := Φ.exists_positive_ray_numbering_of_nodalCycleNumbering b hΦ hc A
  obtain ⟨d', -, hv, hnodes'⟩ := Ψ.exists_positive_ray_numbering_of_nodalCycleNumbering b' hΨ hc' A'
  have hcone (j : ZMod m) : ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ := by
    obtain ⟨σ, h₀, h₁, -⟩ := hnodes j
    exact ⟨σ.val, h₀, h₁⟩
  have hcone' (j : ZMod m) : ∃ τ : Ψ.cones, (v j).toCone ≤ τ ∧ (v (j + 1)).toCone ≤ τ := by
    obtain ⟨τ, h₀, h₁, -⟩ := hnodes' j
    exact ⟨τ.val, h₀, h₁⟩
  obtain ⟨f, ⟨hf, hpic⟩, huniq⟩ :=
    existsUnique_fanEquiv_of_strictRayBoundaryClasses d d' hΦ hΨ hc hc' u v
      (fun j ↦ ⟨hu j, hcone j⟩) (fun j ↦ ⟨hv j, hcone' j⟩) hT hU e he hD
  have hA (j : ZMod m) : A.component j = Φ.boundaryNormalizationComponentEquiv hΦ (u j) :=
    (boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering hΦ A j).symm
  have hA' (j : ZMod m) : A'.component j = Ψ.boundaryNormalizationComponentEquiv hΨ (v j) :=
    (boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering hΨ A' j).symm
  -- The first two matched rays determine the determinant sign in the chosen bases.
  have hdet := f.detDualEquiv_of_matching_adjacent_rays d d' hΦ (hf 0) (hf (0 + 1))
    (hu 0) (hv 0) (hcone 0)
  have haction : (f.boundaryIso hΦ₀ hΨ₀).boundaryCycleAction A A' = 1 := by
    have h := f.boundaryIso_boundaryCycleAction hΦ hΨ A A' hA hA' d d' hu hv false
      (by simpa only [Bool.false_eq_true, ↓reduceIte] using hdet)
    simpa only [Bool.false_eq_true, ↓reduceIte, hf, Equiv.symm_apply_apply,
      ← DihedralGroup.one_def] using h
  refine ⟨f, ⟨haction, hpic⟩, fun g hg ↦ huniq g ⟨?_, hg.2⟩⟩
  intro j
  have h := g.boundaryIso_cycleVertexPerm hΦ hΨ A A' hA hA' j
  simpa only [hg.1, map_one, Equiv.Perm.one_apply] using h.symm

end TauCeti.Toric.Fan
