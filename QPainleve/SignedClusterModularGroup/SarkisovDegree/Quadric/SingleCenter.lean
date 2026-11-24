/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.Basic
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.SectionContraction

import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.Geometry.Toric.Fan.Logarithmic.Subdivision
import QPainleve.Geometry.Toric.Fan.Mutation.Tower
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Decrease

/-!
# The one-center Sarkisov block from a quadric

A high-order smooth center on a quadric becomes a section center in the
exchanged ruling. Mutating there and contracting the negative section gives
a plane resolution of strictly smaller Sarkisov bidegree. Both links preserve
the pole factorization on the original resolution, and the returned point
tower carries its pullback along the inverse resolving isomorphism.

This is Case A of Proposition 8.11 in [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular)
  (hc : Φ.IsComplete) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])

local notation "v" => Fan.Ray.primitiveGenerator (r 0)
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero (r 0)
local notation "hp" => Fan.Ray.hull_primitiveGenerator_mem (r 0)

local notation "hop" => Fan.hull_neg_primitiveGenerator_mem_of_hirzebruch b 0 r hr
local notation "Ψ" => Φ.mutationFan b hv hp hop
local notation "hΨ" => Iff.mpr (Φ.isRegular_mutationFan_iff b hv hp hop) hΦ
local notation "hcΨ" => Iff.mpr (Φ.isComplete_mutationFan_iff b hv hp hop) hc
local notation "s" => r.trans (Φ.mutationFanRayEquiv b hv hp hop)
local notation "hs" => Fan.Ray.mutationFan_hirzebruch_ray_generators_of_section_zero
  (r 0) b hop 0 r hr rfl
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))
local notation "X" => Φ.algebraicRealization
local notation "X'" => Fan.algebraicRealization Ψ
local notation "fX" => (X ↘ S)
local notation "fX'" => (X' ↘ S)
local notation "fP" => (P ↘ S)
local notation "C" => Fan.hirzebruchPicardBasis b 0 hΦ r hr
local notation "B[" A "," h "]" => Fan.boundaryIdeal A (Fan.IsComplete.nonempty_cones h)
local notation "Plane[" d "]" => Fan.projectiveSpace d (Fan.lattice Ψ)
local notation "hcPlane[" d "]" => Fan.isComplete_projectiveSpace d (Fan.lattice Ψ)
local notation "planeIso[" d "]" =>
  Fan.projectivePlaneIso d (Fan.lattice Ψ) ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3))
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "pivotPoint[" c "]" =>
  (Fan.Ray.binomialCenter (r 0) rankTwo (b.detDualEquiv_self v)
    (Fan.Ray.surjective_detCharacter (r 0) b) c) (IsLocalRing.closedPoint ℂ)
local notation "mutationMap[" c "]" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (c : ℂ) hv hp hop)
variable {n : ℕ} {Y : Scheme.{0}} {T : BlowupTower Φ.algebraicRealization (n + 1) Y}
  (hT : IsClosedPointTower Φ.algebraicRealization T) (g : Y ⟶ P)

local notation "firstIndex" => Fin.castAdd n (0 : Fin 1)

section PoleIdeal

variable [Nonempty Φ.cones] [IsIntegral Y] [IsDominant T.toBase]

include hΦ in
private theorem single_high_center_poleIdeal (c : ℂˣ)
    {Z W : Scheme} {U : BlowupTower X' (1 + n) Z} (e : Y ≅ Z)
    (d : Basis (Fin 2) ℤ N) (s₀ : (Ψ).IsSubdivision Plane[d])
    {V₀ : BlowupTower P (1 + (1 + n)) W} (hV : IsClosedPointTower P V₀) (k : Z ≅ W)
    (hmap : T.toBase.toRationalMap.comp mutationMap[c] = (e.hom ≫ U.toBase).toRationalMap)
    (hproj : k.hom ≫ V₀.toBase = U.toBase ≫ s₀.toFanHom.algebraicMap ≫ planeIso[d].hom)
    (D : Y.IdealSheafData) :
    letI : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    letI : Y.Over S := ⟨T.toBase ≫ fX⟩
    letI : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension fX).smooth
    let p₁ := e.hom ≫ U.toBase
    let p₂ := p₁ ≫ s₀.toFanHom.algebraicMap
    ∃ (hp₁ : p₁.IsOver S) (hp₂ : p₂.IsOver S),
      letI := hp₁
      letI := hp₂
      B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
        B[Ψ,hcΨ].comap p₁ = D * ramificationIdealSheaf ℂ p₁ ∧
        B[Plane[d],hcPlane[d]].comap p₂ = D * ramificationIdealSheaf ℂ p₂ ∧
        (B[Plane[d],hcPlane[d]].comap planeIso[d].inv).comap V₀.toBase =
          D.comap (e ≪≫ k).inv * hV.ramificationIdealSheafToBase ℂ := by
  intro p₁ p₂
  let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
  let : SmoothOfRelativeDimension 2 fX := by
    rw [Fan.algebraicRealization_over]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Y.Over S := ⟨T.toBase ≫ fX⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fX
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let hReg := Fan.isRegular_projectiveSpace d (Ψ).lattice
  let : SmoothOfRelativeDimension 2 fX' := by
    rw [Fan.algebraicRealization_over]
    exact rankTwo ▸ (Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  let : SmoothOfRelativeDimension 2 (Plane[d].algebraicRealization ↘ S) := by
    simpa only [Fan.algebraicRealization_over, rankTwo] using
      (Plane[d]).smoothOfRelativeDimension_algebraicRealizationStructureMap hReg
  obtain ⟨hp₁, hpole⟩ := (r 0).mutation_resolution_poleIdeal_iff b hop c hT hΦ hc p₁ D hmap
  let : p₁.IsOver S := hp₁
  let : p₂.IsOver S := inferInstanceAs ((p₁ ≫ s₀.toFanHom.algebraicMap).IsOver S)
  refine ⟨hp₁, ‹_›, fun hD ↦ ?_⟩
  have h₁ := hpole.mp (by simpa only [hT.ramificationIdealSheafToBase_def ℂ] using hD)
  have h₂ := comap_eq_mul_ramificationIdealSheaf_comp ℂ p₁ s₀.toFanHom.algebraicMap 2
    (s₀.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf hReg hΨ hcPlane[d] rankTwo) h₁
  refine ⟨h₁, h₂, ?_⟩
  let a := planeIso[d]
  let t := e ≪≫ k
  have ha : a.hom.IsOver S := ⟨by
    simp only [a, Iso.trans_hom, Category.assoc, over_eq_projToSpec,
      Basis.polynomialProjIso_hom_over, Fan.projectivePlaneIso_hom_toSpecCoeff,
      Fan.algebraicRealization_over]⟩
  let : (p₂ ≫ a.hom).IsOver S := inferInstance
  have ht : t.hom ≫ V₀.toBase = p₂ ≫ a.hom := by
    simpa only [t, p₁, p₂, a, Iso.trans_hom, Category.assoc] using
      congrArg (fun f ↦ e.hom ≫ f) hproj
  let : Smooth (Plane[d].algebraicRealization ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  -- The plane coordinate isomorphism has unit ramification ideal.
  have hPole : (B[Plane[d],hcPlane[d]].comap a.inv).comap (p₂ ≫ a.hom) =
      D * ramificationIdealSheaf ℂ (p₂ ≫ a.hom) := by
    rw [← comap_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      ramificationIdealSheaf_comp ℂ p₂ a.hom 2,
      ramificationIdealSheaf_eq_top_of_isOpenImmersion ℂ a.hom, comap_top, mul_top]
    exact h₂
  rw [← hV.comap_ramificationIdealSheafToBase ℂ t ht, ← ht] at hPole
  simpa only [comap_mul, ← comap_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Scheme.IdealSheafData.comap_id, Category.assoc] using
    congrArg (fun I : Y.IdealSheafData ↦ I.comap t.inv) hPole

end PoleIdeal

variable [Φ.algebraicRealization.IsProjectiveOver ℂ]

/-- The one-point block from a quadric carries a specified plane resolution
across the mutation and the subsequent toric contraction to the plane.
The quadric is written in the frame of the exchanged ruling, so its original
fiber degree is the coefficient of the fiber in the displayed frame. The
selected pivot lies on the chosen section in this frame.
On the original resolving surface, the regular partial composites after the
mutation and the contraction preserve the pole ideal. In the plane point
tower the pole ideal is its pullback along the inverse resolving isomorphism.

If the pivot is the only order greater than half the original fiber degree,
and is bounded by that fiber degree, the plane degree is positive and its
Sarkisov bidegree is strictly smaller. The two new exceptional coordinates
are those of the contracted section and the reverse pivot. Every other
coordinate retains its original relative order. The contraction is a single
toric star blowdown. -/
theorem exists_plane_resolution_of_quadric_single_high_center
    (hg : g ≫ fP = T.toBase ≫ fX) (hbir : Scheme.BirationalOver g (𝟙 P))
    (c : ℂˣ) (j : Fin (n + 1)) (hj : hT.baseCenter j = pivotPoint[c])
    (hfirst : ∀ l < j, hT.baseCenter l ≠ pivotPoint[c]) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    let : SmoothOfRelativeDimension 2 fX := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    let : IsNoetherian X := by
      let : Smooth Φ.algebraicRealizationStructureMap :=
        Φ.smooth_algebraicRealizationStructureMap hΦ
      exact isNoetherian_of_finiteType Φ.algebraicRealizationStructureMap
    let : IsIntegral Y := hT.isIntegral fX
    let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two fX
    let x : Additive (LineBundleClass X) × (Fin (n + 1) → ℤ) :=
      (T.picardMarking hT fX).symm (Additive.ofMul (pullback g H))
    let b₀ := (C).repr x.1 0
    let a₀ := (C).repr x.1 1
    let m := fun l ↦ -x.2 l
    0 < b₀ → b₀ < 2 * m j → m j ≤ b₀ →
      (∀ l ≠ j, 0 ≤ m l ∧ 2 * m l ≤ b₀) →
      ∃ (Z : Scheme) (U : BlowupTower X' (1 + n) Z) (_ : IsClosedPointTower X' U)
        (e : Y ≅ Z) (d : Basis (Fin 2) ℤ N)
        (s₀ : (Ψ).IsSubdivision (Fan.projectiveSpace d (Ψ).lattice))
        (W : Scheme) (V₀ : BlowupTower P (1 + (1 + n)) W) (hV : IsClosedPointTower P V₀)
        (k : Z ≅ W),
        T.toBase.toRationalMap.comp mutationMap[c] = (e.hom ≫ U.toBase).toRationalMap ∧
        k.hom ≫ V₀.toBase = U.toBase ≫ s₀.toFanHom.algebraicMap ≫ planeIso[d].hom ∧
        (k.inv ≫ e.inv ≫ g) ≫ fP = V₀.toBase ≫ fP ∧
        Scheme.BirationalOver (k.inv ≫ e.inv ≫ g) (𝟙 P) ∧
        (letI : Y.Over S := ⟨T.toBase ≫ fX⟩
         letI : Smooth (Y ↘ S) := (hT.smoothOfRelativeDimension fX).smooth
         let p₁ := e.hom ≫ U.toBase
         let p₂ := p₁ ≫ s₀.toFanHom.algebraicMap
         ∀ D : Y.IdealSheafData,
           ∃ (hp₁ : p₁.IsOver S) (hp₂ : p₂.IsOver S),
             letI := hp₁
             letI := hp₂
             B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
               B[Ψ,hcΨ].comap p₁ = D * ramificationIdealSheaf ℂ p₁ ∧
               B[Plane[d],hcPlane[d]].comap p₂ = D * ramificationIdealSheaf ℂ p₂ ∧
               (B[Plane[d],hcPlane[d]].comap planeIso[d].inv).comap V₀.toBase =
                 D.comap (e ≪≫ k).inv * hV.ramificationIdealSheafToBase ℂ) ∧
        let y := (V₀.picardMarking hV fP).symm (Additive.ofMul (pullback (k.inv ≫ e.inv ≫ g) H))
        degree y.1 = b₀ + a₀ - m j ∧
        y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = m j - b₀ ∧
        y.2 (Fin.natAdd 1 firstIndex) = m j - a₀ ∧
        (∀ l : Fin n, y.2 (Fin.natAdd 1 (l.natAdd 1)) = x.2 (j.succAbove l)) ∧
        0 < degree y.1 ∧
        (∀ M' M, planeSarkisovBidegree (degree y.1).toNat M' <
          hirzebruchSarkisovBidegree b₀.toNat M) ∧
        Plane[d].IsTwoRayStarSubdivision Ψ := by
  intro hcones hcones' hdim hnoeth hY hmod x b₀ a₀ m hb hm hmb hsmall
  let := hcones
  let := hcones'
  let := hdim
  let := hnoeth
  let := hY
  let := hmod
  have ⟨hsq, hsum⟩ := hT.homaloidal_intersection_identities_of_hirzebruch b 0 hΦ hc r hr g hg hbir
  have hlt := quadric_sarkisov_degree_decrease_of_single (a := a₀) (m := m) hb j
    (by
      have hmul : 2 * a₀ * b₀ = 2 * b₀ * a₀ := mul_right_comm 2 a₀ b₀
      simpa only [m, neg_sq, Nat.cast_zero, zero_mul, sub_zero, hmul] using hsq)
    (by
      have hadd : 2 * a₀ + 2 * b₀ = 2 * b₀ + 2 * a₀ := add_comm _ _
      simpa only [m, Nat.cast_zero, sub_zero, hadd] using hsum)
    hm.le hmb hsmall
  obtain ⟨Z, U, hU, e, hmap, hg', hbir', _, _, hα, hβ, hfirst', htail⟩ :=
    hT.exists_hirzebruchOne_resolution_of_quadric_mutation b hΦ hc r hr g hg hbir c j hj hfirst
  obtain ⟨d, s₀, W, V₀, hV, k, hproj, hg'', hbir'', hdegree, hvertex, hrem, -, hstar⟩ :=
    hU.exists_plane_resolution_of_hirzebruchOne b hΨ hcΨ s hs (e.inv ≫ g) hg' hbir'
  refine ⟨Z, U, hU, e, d, s₀, W, V₀, hV, k, hmap, hproj,
    by simpa only [Category.assoc] using hg'', by simpa only [Category.assoc] using hbir'',
    single_high_center_poleIdeal b hΦ hc r hr hT c e d s₀ hV k hmap hproj, ?_⟩
  intro y
  have hy : degree y.1 = b₀ + a₀ - m j := by
    simpa only [y, Category.assoc, hα, b₀, a₀, m, sub_neg_eq_add] using hdegree
  have hf : y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = m j - b₀ := by
    have h : y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = a₀ - (b₀ + a₀ - m j) := by
      simpa only [y, Category.assoc, hβ, hα, b₀, a₀, m, sub_neg_eq_add] using hvertex
    omega
  refine ⟨hy, hf, ?_, ?_, hy ▸ hlt.1, ?_, hstar⟩
  · have h : y.2 (Fin.natAdd 1 firstIndex) = -a₀ - x.2 j := by
      simpa only [y, Category.assoc, hfirst', a₀] using hrem firstIndex
    dsimp only [m]
    omega
  · intro l
    simpa only [y, Category.assoc, htail] using hrem (l.natAdd 1)
  · intro M' M
    rw [Prod.Lex.lt_iff, ofLex_planeSarkisovBidegree, ofLex_hirzebruchSarkisovBidegree]
    refine Or.inl ?_
    rw [hy]
    omega

end QPainleve.BlowupTower.IsClosedPointTower
