/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Subdivision
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.SmoothCenter

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.PoleIdeal
import QPainleve.Geometry.Toric.Fan.Mutation.Tower

/-!
# Logarithmic Sarkisov decrease at a plane edge

The blowup of the opposite toric vertex, the mutation at the lifted edge
center, and the quadric ruling exchange preserve the reduced pole divisor on
one nodal refinement. This is the smooth plane case of Proposition 8.11 and
the pole comparison in Theorem 8.4 of [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra TauCeti.Toric
open Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Plane" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "fP" => (Plane ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun ℂ (Fin 3))
local notation "J[" p "]" => Scheme.Hom.ker (Scheme.fromSpecResidueField Plane p)
local notation "X[" U "]" => Fan.algebraicRealization U
local notation "f[" U "]" => (X[U] ↘ S)
local notation "B[" U "," h "]" => Fan.boundaryIdeal U (Fan.IsComplete.nonempty_cones h)
local notation "π[" s "]" => FanHom.algebraicMap (Fan.IsSubdivision.toFanHom s)

variable {Y : Scheme} {n : ℕ} {T : BlowupTower Plane (n + 1) Y}
  (hT : IsClosedPointTower Plane T)

section Edge

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (regΦ : Φ.IsRegular) (hcΦ : Φ.IsComplete)
  (b : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1])
  (c : ℂˣ)

variable {p₀ : Plane} (e₀ : X[Φ] ≅ (J[p₀]).blowup)

local notation "π" => Iso.hom e₀ ≫ Scheme.IdealSheafData.blowupToBase (J[p₀])
local notation "ρ" => (r 2 : Fan.Ray Φ)
local notation "v" => Fan.Ray.primitiveGenerator ρ
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center" =>
  Fan.Ray.binomialCenter ρ (m := LinearMap.toAddMonoidHom (Basis.detDualEquiv b v))
    rankTwo (b.detDualEquiv_self v) (Fan.Ray.surjective_detCharacter ρ b) c
local notation "u" => center (IsLocalRing.closedPoint ℂ)
local notation "hOpp" =>
  Eq.mpr (congrArg (fun x : N ↦ hull ℝ {i x} ∈ Fan.cones Φ)
    (Eq.trans (congrArg Neg.neg (congrFun hr 2))
      (Eq.trans (neg_neg (b 0)) (Eq.symm (congrFun hr 0)))))
    (Fan.Ray.hull_primitiveGenerator_mem (r 0))
local notation "hv" => Fan.Ray.primitiveGenerator_ne_zero ρ
local notation "hPivotCone" => Fan.Ray.hull_primitiveGenerator_mem ρ
local notation "Ψ" => Fan.mutationFan Φ b hv hPivotCone hOpp
local notation "regΨ" => Iff.mpr (Fan.isRegular_mutationFan_iff Φ b hv hPivotCone hOpp) regΦ
local notation "hcΨ" => Iff.mpr (Fan.isComplete_mutationFan_iff Φ b hv hPivotCone hOpp) hcΦ
local notation "s" => Equiv.trans r (Fan.mutationFanRayEquiv Φ b hv hPivotCone hOpp)
local notation "μ" =>
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap Φ b (c : ℂ) hv hPivotCone hOpp)
local notation "C'[" d' "," hd' "]" => Fan.hirzebruchPicardBasis d' 0 regΨ s hd'

include regΦ b in
private theorem plane_edge_vertex_pole {Δ : Fan i}
    (regΔ : Δ.IsRegular) (hcΔ : Δ.IsComplete) (t : Φ.IsSubdivision Δ)
    (eP : X[Δ] ≅ Plane) [eP.hom.IsOver S]
    {A : Scheme} [A.Over S] [IsIntegral A] [SmoothOfRelativeDimension 2 (A ↘ S)]
    (a : A ⟶ X[Φ]) [a.IsOver S] [IsDominant a] (f : A ⟶ Plane) [f.IsOver S]
    (hf : a ≫ π[t] ≫ eP.hom = f) (D : A.IdealSheafData) :
    letI : Smooth (A ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    (B[Δ,hcΔ].comap eP.inv).comap f = D * ramificationIdealSheaf ℂ f →
      B[Φ,hcΦ].comap a = D * ramificationIdealSheaf ℂ a := by
  let : Nonempty Φ.cones := hcΦ.nonempty_cones
  let : Nonempty Δ.cones := hcΔ.nonempty_cones
  let : Smooth (A ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : SmoothOfRelativeDimension 2 f[Φ] :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap regΦ
  let : SmoothOfRelativeDimension 2 f[Δ] :=
    rankTwo ▸ Δ.smoothOfRelativeDimension_algebraicRealizationStructureMap regΔ
  let : Smooth f[Φ] := SmoothOfRelativeDimension.smooth 2 _
  let : Smooth f[Δ] := SmoothOfRelativeDimension.smooth 2 _
  intro hpole
  let g := π[t] ≫ eP.hom
  have hBoundary : (B[Δ,hcΔ].comap eP.inv).comap eP.hom = B[Δ,hcΔ] := by
    rw [← comap_comp, eP.hom_inv_id, Scheme.IdealSheafData.comap_id]
  have hRam : ramificationIdealSheaf ℂ g = ramificationIdealSheaf ℂ π[t] := by
    dsimp only [g]
    rw [ramificationIdealSheaf_comp ℂ π[t] eP.hom 2,
      ramificationIdealSheaf_eq_top_of_isOpenImmersion ℂ eP.hom, comap_top, mul_top]
  have hB : (B[Δ,hcΔ].comap eP.inv).comap g = B[Φ,hcΦ] * ramificationIdealSheaf ℂ g := by
    rw [comap_comp, hBoundary, hRam]
    exact t.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf regΔ regΦ hcΔ rankTwo
  have hCart : ((ramificationIdealSheaf ℂ g).comap a).IsEffectiveCartier := by
    rw [hRam]
    exact (t.isEffectiveCartier_ramificationIdealSheaf regΔ regΦ hcΔ rankTwo).comap_of_isDominant a
  have hcomp : a ≫ g = f := hf
  apply (comap_eq_mul_ramificationIdealSheaf_comp_iff ℂ a g 2 hCart hB).mp
  exact (congrArg (B[Δ,hcΔ].comap eP.inv).comap hcomp).trans
    (hpole.trans (congrArg (D * ·) (ramificationIdealSheaf_congr ℂ hcomp).symm))

variable (j : Fin (n + 1)) (g : Y ⟶ Plane)
  (hg : g ≫ fP = T.toBase ≫ fP) (hbir : Scheme.BirationalOver g (𝟙 Plane))
  {Δ : Fan i} (regΔ : Δ.IsRegular) (hcΔ : Δ.IsComplete) (t : Φ.IsSubdivision Δ)
  (eP : X[Δ] ≅ Plane) [eP.hom.IsOver S]

local notation "E" => Scheme.IdealSheafData.comap B[Δ,hcΔ] (Iso.inv eP)
local notation "mark[" T "," h "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T h fP) (Additive.ofMul (pullback g H))

include b regΔ in
private theorem isNodeOfReducedBoundary_plane_vertex (σ : Δ.cones)
    (hσ : Nat.card (ToricRay σ.val) = 2) :
    (E).IsNodeOfReducedBoundary fP
      (eP.hom (Δ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))) := by
  let : eP.inv.IsOver S := inferInstance
  have hn := Δ.isNodeOfReducedBoundary_distinguishedPointHom regΔ σ rankTwo hσ
  rw [← comp_over eP.inv S]
  have hx (x : X[Δ]) : eP.inv (eP.hom x) = x := by
    rw [← Scheme.Hom.comp_apply, eP.hom_inv_id]
    rfl
  exact (B[Δ,hcΔ].isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion f[Δ] eP.inv _).mpr
    (by simpa only [hx, Fan.algebraicRealization_over] using hn)

include hg hbir regΔ in
/-- At a proper high-order center on a plane edge, the opposite-vertex blowup,
mutation and ruling exchange are regular on one nodal refinement. Each partial
composite has pole ideal the reduced total transform of the original pole
divisor. The final tower has the same pole factorization in its own coordinates,
and its resolving morphism to the plane has smaller Sarkisov bidegree. -/
theorem exists_sarkisov_decrease_of_logarithmic_plane_edge
    (hπ : π = π[t] ≫ eP.hom)
    (hE : (J[p₀]).comap π = Φ.rayBoundaryIdeal regΦ (r 0))
    (σ : Δ.cones) (hσ : Nat.card (ToricRay σ.val) = 2)
    (hvertex : eP.hom (Δ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)) = p₀)
    (hj : hT.baseCenter j = π u)
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hhigh : let w := mark[T,hT,g]; degree w.1 < 3 * (-w.2 j))
    (D : Y.IdealSheafData) (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ fP))
    (hpole : (E).comap T.toBase = D * hT.ramificationIdealSheafToBase ℂ) :
    letI : Nonempty (Φ).cones := (hcΦ).nonempty_cones
    letI : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    letI : SmoothOfRelativeDimension 2 f[Ψ] :=
      Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d f[Ψ]) rankTwo)
      ((Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap regΨ)
    ∃ (A : Scheme) (q : A ⟶ Y) (a : A ⟶ X[Φ])
      (d' : Basis (Fin 2) ℤ N)
      (hd' : (fun l ↦ (s l).primitiveGenerator) = ![d' 0, d' 1, -d' 0, (0 : ℤ) • d' 0 - d' 1])
      (m : ℕ) (Z : Scheme) (U : BlowupTower X[Ψ] m Z) (hU : IsClosedPointTower X[Ψ] U)
      (e : A ≅ Z) (p : A ⟶ X[Ψ]) (_ : IsIntegral A) (_ : IsDominant a)
      (k : ℕ) (W : Scheme) (R : BlowupTower Y k W) (e₁ : A ≅ W)
      (_ : IsNodalBoundaryTower D (T.toBase ≫ fP) (𝟙 Y) R),
      let τ := (Fan.quadricRulingExchange d' regΨ hcΨ s hd').toFanHom.algebraicMap
      let g' := e.inv ≫ q ≫ g
      letI : A.Over S := ⟨a ≫ f[Φ]⟩
      let D' := (D.comap q).radical
      ∃ (hA : SmoothOfRelativeDimension 2 (A ↘ S)) (ha : a.IsOver S) (hp : p.IsOver S),
        letI := hA.smooth
        letI := ha
        letI := hp
        k ≤ 1 ∧ e₁.hom ≫ R.toBase = q ∧
        a ≫ π[t] ≫ eP.hom = q ≫ T.toBase ∧
        a.toRationalMap.comp μ = p.toRationalMap ∧
        e.hom ≫ U.toBase = p ≫ τ ∧
        B[Φ,hcΦ].comap a = D' * ramificationIdealSheaf ℂ a ∧
        B[Ψ,hcΨ].comap p = D' * ramificationIdealSheaf ℂ p ∧
        B[Ψ,hcΨ].comap (p ≫ τ) = D' * ramificationIdealSheaf ℂ (p ≫ τ) ∧
        B[Ψ,hcΨ].comap U.toBase = D'.comap e.inv * hU.ramificationIdealSheafToBase ℂ ∧
        g' ≫ fP = U.toBase ≫ f[Ψ] ∧ Scheme.BirationalOver g' (𝟙 Plane) ∧
        let w := mark[T,hT,g]
        let y := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback g' H))
        (C'[d',hd']).repr y.1 1 = degree w.1 + w.2 j ∧
        0 < (C'[d',hd']).repr y.1 1 ∧
        hirzebruchSarkisovBidegree ((C'[d',hd']).repr y.1 1).toNat (∑ l, (-y.2 l).toNat) <
          planeSarkisovBidegree (degree w.1).toNat (∑ l, (-w.2 l).toNat) := by
  let : Nonempty Φ.cones := hcΦ.nonempty_cones
  let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Φ] :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap regΦ
  let : SmoothOfRelativeDimension 2 f[Ψ] :=
    Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d f[Ψ]) rankTwo)
      ((Ψ).smoothOfRelativeDimension_algebraicRealizationStructureMap regΨ)
  have hπOver : π ≫ fP = f[Φ] := by
    rw [hπ, Category.assoc, comp_over eP.hom S, comp_over π[t] S]
  have hsection : (Δ.distinguishedPointHom σ ≫ eP.hom) ≫ fP = 𝟙 S := by
    rw [Category.assoc, comp_over eP.hom S, Fan.algebraicRealization_over,
      Fan.distinguishedPointHom_comp_algebraicRealizationStructureMap]
  have hp₀ : IsClosed ({p₀} : Set Plane) := by
    have hpoint := (Scheme.Hom.comp_apply (Δ.distinguishedPointHom σ) eP.hom
      (IsLocalRing.closedPoint ℂ)).trans hvertex
    exact hpoint ▸ isClosed_singleton_of_section hsection
  obtain ⟨A, q, k', R', hR', d', hd', m, Z, U, hU, e, p, hI, hdom, hqIso, hqBlowup,
    habase, hmut, hτ, hg', hb', hdegree, hpos, hlt⟩ :=
    hT.exists_sarkisov_decrease_of_plane_edge j g hg hbir regΦ hcΦ b r hr c hp₀ e₀
      hπOver hE hj hfirst hhigh
  have hnode := isNodeOfReducedBoundary_plane_vertex b regΔ hcΔ eP σ hσ
  rw [hvertex] at hnode
  obtain ⟨k, W, R, e₁, hk, hR, he₁⟩ :=
    hT.exists_nodal_refinement_of_point_preparation q hnode hpole hqIso hqBlowup
  let a := R'.toBase
  let : Y.Over S := ⟨T.toBase ≫ fP⟩
  let : A.Over S := ⟨a ≫ f[Φ]⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fP
  let hA : SmoothOfRelativeDimension 2 (A ↘ S) := hR'.smoothOfRelativeDimension f[Φ]
  let := hA
  let : Smooth (A ↘ S) := hA.smooth
  let : q.IsOver S := ⟨by
    exact ((reassoc_of% habase) fP).symm.trans (congrArg (a ≫ ·) hπOver)⟩
  let : T.toBase.IsOver S := ⟨rfl⟩
  let ha : a.IsOver S := ⟨rfl⟩
  let := ha
  let D' := (D.comap q).radical
  let : IsIntegral Y := hT.isIntegral fP
  let : IsNoetherian Y := T.isNoetherian
  have hqPole := hR.comap_eq_radical_mul_ramificationIdealSheaf_of_iso hD hN e₁ q he₁
  have hBasePole := comap_eq_mul_ramificationIdealSheaf_comp ℂ q T.toBase 2
    ((hT.ramificationIdealSheafToBase_def ℂ) ▸ hpole) hqPole
  have habase' : a ≫ π[t] ≫ eP.hom = q ≫ T.toBase := hπ ▸ habase
  have haPole := plane_edge_vertex_pole regΦ hcΦ b regΔ hcΔ t eP a _ habase' D' hBasePole
  obtain ⟨hp, hiff⟩ := (ρ).mutation_resolution_poleIdeal_iff b hOpp c hR' regΦ hcΦ p D' hmut
  have hpPole := hiff.mp ((hR'.ramificationIdealSheafToBase_def ℂ).symm ▸ haPole)
  let := hp
  let F := Fan.quadricRulingExchange d' regΨ hcΨ s hd'
  let τ := F.toFanHom.algebraicMap
  have hτPole := comap_eq_mul_ramificationIdealSheaf_comp ℂ p τ 2 (D := B[Ψ,hcΨ])
    (P := B[Ψ,hcΨ]) (by
      rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top]
      exact F.comap_boundaryIdeal_algebraicMap _ _) hpPole
  have hUPole := congrArg (fun I : A.IdealSheafData ↦ I.comap e.inv) hτPole
  rw [comap_mul, ← hU.comap_ramificationIdealSheafToBase ℂ e hτ,
    ← comap_comp, ← hτ, e.inv_hom_id_assoc, ← comap_comp, e.inv_hom_id,
    Scheme.IdealSheafData.comap_id] at hUPole
  exact ⟨A, q, a, d', hd', m, Z, U, hU, e, p, hI, hdom, k, W, R, e₁, hR,
    hA, ha, hp, hk, he₁, habase', hmut, hτ, haPole, hpPole, hτPole, hUPole, hg', hb',
    hdegree, hpos, hlt⟩

end Edge

end QPainleve.BlowupTower.IsClosedPointTower
