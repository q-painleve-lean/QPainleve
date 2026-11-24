/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nef
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef.Pullback
import QPainleve.Geometry.Toric.Fan.HalfPlane
import QPainleve.Geometry.Toric.Fan.Picard.Ruling
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Fiber degree bounds on Hirzebruch resolutions

The ruling of a Hirzebruch fan provides an effective Cartier representative of the fiber
class through each closed point. The fiber degree of a nef class in the ordered point-blowup
marking bounds each base order, including at infinitely near centers. For a resolved line
system this is the bound used at corner and section pivots in Lutz's appendix to Hacking
and Keating, [*Homological mirror symmetry for log Calabi–Yau surfaces*, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public section

open AlgebraicGeometry CategoryTheory Module PointedCone TauCeti.Toric
open TauCeti.AlgebraicGeometry LineBundleClass Chow

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X" => Φ.algebraicRealization
local notation "f" => (X ↘ S)
local notation "C" => Φ.hirzebruchPicardBasis b e hΦ r hr
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)

namespace TauCeti.Toric.Fan

variable [Nonempty Φ.cones]

/-- The fiber class of a Hirzebruch fan has an effective Cartier representative through
every closed point, obtained as the scheme-theoretic fiber of the ruling at the point's image. -/
theorem exists_isEffectiveCartier_mem_support_hirzebruchPicardBasis_zero
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ (D : (X).IdealSheafData) (hD : D.IsEffectiveCartier), x ∈ D.support ∧
      Additive.ofMul (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ = C 0 := by
  classical
  let m := (b.coord 1).toAddMonoidHom
  have h₀ : hull ℝ {i (b 0)} ∈ Φ.cones := by
    simpa [congrFun hr (0 : Fin 4)] using (r 0).hull_primitiveGenerator_mem
  have h₂ : hull ℝ {i (-b 0)} ∈ Φ.cones := by
    simpa [congrFun hr (2 : Fin 4)] using (r 2).hull_primitiveGenerator_mem
  have h (σ : Φ.cones) : (∀ v ∈ σ.val, 0 ≤ Φ.lattice.realCharacter m v) ∨
      ∀ v ∈ σ.val, Φ.lattice.realCharacter m v ≤ 0 := by
    have hrev : (1 : Fin 2).rev = 0 := by decide
    simpa only [m, IsIntegralLattice.realCharacter_coord, Basis.coord_apply] using
      Φ.nonneg_or_nonpos_basis_repr_on_cone b 1 σ
        (fun _ ↦ by simpa only [hrev] using h₀) (fun _ ↦ by simpa only [hrev] using h₂)
  have hm : m ≠ 0 := by
    intro hz
    have hval := DFunLike.congr_fun hz (b 1)
    simp [m] at hval
  have hdim : SmoothOfRelativeDimension 2 f :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Smooth f := hdim.smooth
  let q := Φ.characterRuling m h
  let p := pointOfClosedPoint f x hx ≫ q
  have hp : p ≫ (projectiveLine ℂ ↘ S) = 𝟙 S := by
    simpa only [p, Category.assoc, comp_over q S] using pointOfClosedPoint_comp f x hx
  have : IsClosedImmersion p := p.isClosedImmersion_of_comp_eq_id hp
  let hD := Φ.isEffectiveCartier_characterRuling_fiber m h hm p hp
  refine ⟨p.ker.comap q, hD, ?_, ?_⟩
  · rw [← SetLike.mem_coe, Scheme.IdealSheafData.support_comap,
      TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage, Scheme.Hom.support_ker,
      p.isClosedEmbedding.isClosed_range.closure_eq]
    refine ⟨IsLocalRing.closedPoint ℂ, (Scheme.Hom.comp_apply _ _ _).trans ?_⟩
    exact congrArg q (pointOfClosedPoint_apply f x hx (IsLocalRing.closedPoint ℂ))
  · have hv : (fun ρ : Φ.Ray ↦ max (m ρ.primitiveGenerator) 0) = Pi.single (r 1) 1 := by
      funext ρ
      obtain ⟨j, rfl⟩ := r.surjective ρ
      fin_cases j <;> simp [m, congrFun hr, Basis.coord_apply]
    have hclass := Φ.toLineBundleClass_characterRuling_fiber m h hm p hp hΦ
    simpa only [Scheme.IdealSheafData.IsEffectiveCartier.toLineBundleClass_toCartierDivisor,
      hv, hirzebruchPicardBasis_apply_zero] using hclass

end TauCeti.Toric.Fan

namespace QPainleve.BlowupTower.IsClosedPointTower

variable [Φ.algebraicRealization.IsProjectiveOver ℂ] (hc : Φ.IsComplete)
  {Y : Scheme} {n : ℕ} {T : BlowupTower Φ.algebraicRealization n Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T)

include hT in
/-- The fiber degree of the base class bounds each base order of a marked nef class
on a point blowup tower of a complete regular Hirzebruch fan. -/
theorem neg_exceptionalCoeff_le_hirzebruch_fiber_degree
    (v : Additive (LineBundleClass X) × (Fin n → ℤ))
    (hv : (T.picardHom v).toMul.IsNef ℂ (T.toBase ≫ f)) (j : Fin n) :
    let := hc.nonempty_cones
    (-v.2 j) ≤ (C).repr v.1 1 := by
  intro hcones
  let := hcones
  let : SmoothOfRelativeDimension 2 f :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : IsNoetherian X := isNoetherian_of_finiteType f
  obtain ⟨D, hD, hj, hClass⟩ := Φ.exists_isEffectiveCartier_mem_support_hirzebruchPicardBasis_zero
    b e hΦ r hr _ (hT.isClosed_baseCenter j)
  have hBound := hT.neg_exceptionalCoeff_le_classIntersectionNumber_of_mem_support hv j hD hj
  rw [← toMul_ofMul (mk hD.toInvertibleSheaf)⁻¹, ← intersectionBilinForm_apply, hClass,
    (Φ.hirzebruchPicardBasis_intersection_repr b e hΦ r hr hc v.1).1] at hBound
  exact hBound

open TauCeti.SymmetricAlgebra

local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)

/-- Every base order of a resolved plane line system on a Hirzebruch surface is at most
the fiber degree of the system. The bound holds at corners, at smooth points on
sections and fibers, and at infinitely near centers. -/
theorem base_order_le_hirzebruch_fiber_degree
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f) (j : Fin n) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : SmoothOfRelativeDimension 2 f :=
      rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v : Additive (LineBundleClass X) × (Fin n → ℤ) :=
      (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    (-v.2 j) ≤ (C).repr v.1 1 := by
  intro hcones hdim hnoeth v
  let := hcones
  let := hdim
  let := hnoeth
  let : Y.Over S := ⟨T.toBase ≫ f⟩
  have : g.IsOver S := ⟨hg⟩
  have hH : (H).IsAmple := isAmple_twistingSheaf ℂ (Fin 3 → ℂ) Nat.one_pos
  have hClass : (T.picardHom v).toMul = pullback g H := by
    rw [← picardMarking_apply _ hT f, LinearEquiv.apply_symm_apply, toMul_ofMul]
  exact hT.neg_exceptionalCoeff_le_hirzebruch_fiber_degree b e hΦ r hr hc v
    (hClass.symm ▸ hH.isNef.pullback g) j

end QPainleve.BlowupTower.IsClosedPointTower
