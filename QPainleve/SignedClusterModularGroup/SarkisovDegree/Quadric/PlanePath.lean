/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.SingleCenter

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# The resolved path from a quadric to a plane

Mutation at a smooth point of a section and contraction of the negative
section form a resolved path on the original surface. The terminal plane
point tower carries the prescribed target map and has degree equal to the
sum of the two ruling coefficients minus the selected base order.

See Case A of Proposition 8.11 in [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Scheme.IdealSheafData Fan Fan.LogarithmicProjection
open scoped Sarkisov

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
local notation "X[" Γ "]" => Fan.algebraicRealization Γ
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "f[" Γ "]" => (X[Γ] ↘ S)
local notation "fP" => (P ↘ S)
local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "B[" Γ "," h "]" => Fan.boundaryIdeal Γ (Fan.IsComplete.nonempty_cones h)
local notation "Π[" d "]" => Fan.projectiveSpace d (Fan.lattice Ψ)
local notation "hcΠ[" d "]" => Fan.isComplete_projectiveSpace d (Fan.lattice Ψ)
local notation "π[" s "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom s)
local notation "planeIso[" d "]" =>
  Fan.projectivePlaneIso d (Fan.lattice Ψ) ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3))
local notation "mutationMap[" c "]" =>
  Scheme.PartialMap.toRationalMap (Φ.mutationPartialMap b (c : ℂ) hv hp hop)
local notation "pivotPoint[" c "]" =>
  (Fan.Ray.binomialCenter (r 0) rankTwo (b.detDualEquiv_self v)
    (Fan.Ray.surjective_detCharacter (r 0) b) c) (IsLocalRing.closedPoint ℂ)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))

variable {Y : Scheme} {n : ℕ} {T : BlowupTower X[Φ] (n + 1) Y}
  (hT : IsClosedPointTower X[Φ] T) (g : Y ⟶ P)

section Path

variable [Nonempty Φ.cones] [IsIntegral Y] [Y.Over S]
  [SmoothOfRelativeDimension 2 (Y ↘ S)] {D : Y.IdealSheafData}

include hΦ hc in
private theorem exists_quadric_plane_sarkisov_path
    (p₀ : Y ⟶ X[Φ]) [p₀.IsOver S] [IsDominant p₀]
    (hPole : letI : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      B[Φ,hc].comap p₀ = D * ramificationIdealSheaf ℂ p₀)
    (c : ℂˣ) (m : Y ⟶ X[Ψ]) [m.IsOver S] [IsDominant m]
    (hm : p₀.toRationalMap.comp mutationMap[c] = m.toRationalMap)
    (hmPole : letI : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      B[Ψ,hcΨ].comap m = D * ramificationIdealSheaf ℂ m)
    (d : Basis (Fin 2) ℤ N) (hs : (Π[d]).IsTwoRayStarSubdivision Ψ)
    (h₂ : letI : Nonempty (Fan.cones Ψ) := (hcΨ).nonempty_cones
      letI : Nonempty (Π[d]).cones := (hcΠ[d]).nonempty_cones
      letI : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
      B[Π[d],hcΠ[d]].comap (m ≫ π[hs.isSubdivision]) =
        D * ramificationIdealSheaf ℂ (m ≫ π[hs.isSubdivision])) :
    letI : Nonempty (Fan.cones Ψ) := (hcΨ).nonempty_cones
    letI : Nonempty (Π[d]).cones := (hcΠ[d]).nonempty_cones
    let A : LogarithmicProjection i D :=
      ⟨Φ, hΦ, hc, p₀, inferInstance, inferInstance, hPole⟩
    ∃ (B : LogarithmicProjection i D) (p : SarkisovPath A B),
      B.fan = Π[d] ∧ B.hom ≍ m ≫ π[hs.isSubdivision] ∧ p.length = 2 ∧
        p.rationalMap ≍ mutationMap[c].comp (π[hs.isSubdivision]).toRationalMap := by
  let : Nonempty (Fan.cones Ψ) := (hcΨ).nonempty_cones
  let : Nonempty (Π[d]).cones := (hcΠ[d]).nonempty_cones
  intro A
  let M : LogarithmicProjection i D := ⟨Ψ, hΨ, hcΨ, m, inferInstance, inferInstance, hmPole⟩
  let B : LogarithmicProjection i D := ⟨Π[d], Fan.isRegular_projectiveSpace ..,
    Fan.isComplete_projectiveSpace .., m ≫ π[hs.isSubdivision], inferInstance, inferInstance, h₂⟩
  let μ : SarkisovStep A M := ⟨mutationMap[c], .mutation b (r 0) c hop, hm⟩
  let β : StarStep M B := .blowdown hs rfl
  let p : SarkisovPath A B := (Quiver.Path.nil.cons μ).cons β.toSarkisovStep
  refine ⟨B, p, rfl, HEq.rfl, by simp [p], ?_⟩
  have hmap : (m ≫ π[hs.isSubdivision]).toRationalMap =
      p₀.toRationalMap.comp (mutationMap[c].comp (π[hs.isSubdivision]).toRationalMap) := by
    rw [Scheme.RationalMap.comp_toRationalMap, Scheme.RationalMap.comp_compHom,
      ← Scheme.Hom.toRationalMap_compHom]
    exact (congrArg (fun f : Y ⤏ X[Ψ] ↦ f.compHom π[hs.isSubdivision]) hm).symm
  exact heq_of_eq (p₀.toRationalMap.comp_left_injective (p.comp_rationalMap.trans hmap))

end Path

/-- Mutation at the first center over a smooth point of the chosen quadric
section, followed by contraction of the negative section, gives a two-step
Sarkisov path on the specified resolving surface. Its final plane resolution
retains the prescribed target map and pole ideal. The new degree is positive,
and the exceptional coordinates away from the pivot keep their original order. -/
theorem exists_sarkisov_path_of_quadric_smooth_center
    (hg : g ≫ fP = T.toBase ≫ f[Φ]) (hbir : Scheme.BirationalOver g (𝟙 P))
    (c : ℂˣ) (j : Fin (n + 1)) (hj : hT.baseCenter j = pivotPoint[c])
    (hfirst : ∀ l < j, hT.baseCenter l ≠ pivotPoint[c]) (D : Y.IdealSheafData) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : Nonempty (Fan.cones Ψ) := (hcΨ).nonempty_cones
    letI : SmoothOfRelativeDimension 2 f[Φ] := by
      rw [Fan.algebraicRealization_over]
      exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    letI : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
    letI : IsNoetherian X[Φ] := by
      let : Smooth f[Φ] := SmoothOfRelativeDimension.smooth 2 _
      exact isNoetherian_of_finiteType f[Φ]
    letI : IsIntegral Y := hT.isIntegral f[Φ]
    let x := (T.picardMarking hT f[Φ]).symm (Additive.ofMul (pullback g H))
    let b₀ := (Φ.hirzebruchPicardBasis b 0 hΦ r hr).repr x.1 0
    let a₀ := (Φ.hirzebruchPicardBasis b 0 hΦ r hr).repr x.1 1
    let m := fun l ↦ -x.2 l
    B[Φ,hc].comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ →
    ∃ (d : Basis (Fin 2) ℤ N) (hs : (Π[d]).IsTwoRayStarSubdivision Ψ)
      (A B : LogarithmicProjection i D) (p : SarkisovPath A B)
      (Z : Scheme) (U : BlowupTower P (1 + (1 + n)) Z) (hU : IsClosedPointTower P U)
      (e : Y ≅ Z),
      letI : Nonempty (Π[d]).cones := (hcΠ[d]).nonempty_cones
      A.fan = Φ ∧ A.hom ≍ T.toBase ∧ B.fan = Π[d] ∧
      B.hom ≍ e.hom ≫ U.toBase ≫ planeIso[d].inv ∧ p.length = 2 ∧
      p.rationalMap ≍ mutationMap[c].comp (π[hs.isSubdivision]).toRationalMap ∧
      (e.inv ≫ g) ≫ fP = U.toBase ≫ fP ∧ Scheme.BirationalOver (e.inv ≫ g) (𝟙 P) ∧
      (B[Π[d],hcΠ[d]].comap planeIso[d].inv).comap U.toBase =
        D.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
      let y := (U.picardMarking hU fP).symm (Additive.ofMul (pullback (e.inv ≫ g) H))
      degree y.1 = b₀ + a₀ - m j ∧
      y.2 (Fin.castAdd (1 + n) (0 : Fin 1)) = m j - b₀ ∧
      y.2 (Fin.natAdd 1 (Fin.castAdd n (0 : Fin 1))) = m j - a₀ ∧
      (∀ l : Fin n, y.2 (Fin.natAdd 1 (l.natAdd 1)) = x.2 (j.succAbove l)) ∧
      0 < degree y.1 := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty (Fan.cones Ψ) := (hcΨ).nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Φ] := by
    rw [Fan.algebraicRealization_over]
    exact rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : Y.Over S := ⟨T.toBase ≫ f[Φ]⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[Φ]
  let : IsNoetherian X[Φ] := by
    let : Smooth f[Φ] := SmoothOfRelativeDimension.smooth 2 _
    exact isNoetherian_of_finiteType f[Φ]
  let : IsIntegral Y := hT.isIntegral f[Φ]
  intro x b₀ a₀ m hPole
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[Φ]
  have hA := (hT.ramificationIdealSheafToBase_def ℂ) ▸ hPole
  let A : LogarithmicProjection i D := ⟨Φ, hΦ, hc, T.toBase, inferInstance, inferInstance, hA⟩
  obtain ⟨W, U, hU, e, d, hstar, Z, V₀, hV, k, hmap, hproj, hg', hbir', hpole, hcoords⟩ :=
    hT.exists_plane_resolution_of_quadric_mutation b hΦ hc r hr g hg hbir c j hj hfirst
  obtain ⟨hdegree, hvertex, hpivot, hrest, hpos⟩ := hcoords
  let : Nonempty (Π[d]).cones := (hcΠ[d]).nonempty_cones
  obtain ⟨hmOver, hpOver, hPoles⟩ := hpole D
  let m' := e.hom ≫ U.toBase
  let : m'.IsOver S := hmOver
  let : (m' ≫ π[hstar.isSubdivision]).IsOver S := hpOver
  obtain ⟨hMutPole, hContractPole, hPlanePole⟩ := hPoles hPole
  let : SmoothOfRelativeDimension 2 f[Ψ] := by
    rw [Fan.algebraicRealization_over]
    exact rankTwo ▸ (Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
  let : IsModification U.toBase := hU.isModification_of_smoothOfRelativeDimension_two f[Ψ]
  let : IsDominant m' := inferInstanceAs (IsDominant (e.hom ≫ U.toBase))
  obtain ⟨B, p, hB, hBhom, hlen, hpath⟩ :=
    exists_quadric_plane_sarkisov_path b hΦ hc r hr T.toBase hA c m' hmap hMutPole
      d hstar hContractPole
  let a := planeIso[d]
  have hEndpoint : m' ≫ π[hstar.isSubdivision] = (e ≪≫ k).hom ≫ V₀.toBase ≫ a.inv := by
    have hToPlane : k.hom ≫ V₀.toBase = U.toBase ≫ π[hstar.isSubdivision] ≫ a.hom := hproj
    have h := congrArg (fun f ↦ e.hom ≫ f ≫ a.inv) hToPlane
    simpa only [m', Iso.trans_hom, Category.assoc, a.hom_inv_id, Category.comp_id] using h.symm
  refine ⟨d, hstar, A, B, p, Z, V₀, hV, e ≪≫ k, rfl, HEq.rfl, hB,
    hBhom.trans (heq_of_eq hEndpoint), hlen, hpath, ?_, ?_, hPlanePole, ?_⟩
  · simpa only [Iso.trans_inv, Category.assoc] using hg'
  · simpa only [Iso.trans_inv, Category.assoc] using hbir'
  · simpa only [Iso.trans_inv, Category.assoc] using
      And.intro hdegree ⟨hvertex, hpivot, hrest, hpos⟩

end QPainleve.BlowupTower.IsClosedPointTower
