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

variable (k₀ : Type) [Field k₀] [IsAlgClosed k₀]

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Plane" => Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))
local notation "fP" => (Plane ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k₀ (Fin 3 → k₀) 1)
local notation "degree" => Module.Basis.picardTwistEquiv (Pi.basisFun k₀ (Fin 3))
local notation "J[" coeff "," p "]" => Scheme.Hom.ker
  (Scheme.fromSpecResidueField (Proj (homogeneousSubmodule coeff (Fin 3 → coeff))) p)
local notation "X[" coeff "," U "]" => Fan.finiteFanScheme coeff U
local notation "f[" U "]" => (X[k₀,U] ↘ S)
local notation "B[" U "," h "]" => Fan.toricBoundaryIdeal k₀ U (Fan.IsComplete.nonempty_cones h)
local notation "π[" s "]" => FanHom.finiteFanSchemeHom k₀ (Fan.IsSubdivision.toFanHom s)

variable {Y : Scheme} {n : ℕ} {T : BlowupTower (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀)))
  (n + 1) Y}
  (hT : IsClosedPointTower (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))) T)

section Edge

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {Φ : Fan i} (regΦ : Φ.IsRegular) (hcΦ : Φ.IsComplete)
  (b : Basis (Fin 2) ℤ N) (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (1 : ℤ) • b 0 - b 1])
  (c : k₀ˣ)

variable {p₀ : (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀)))} (e₀ : X[k₀,Φ] ≅ (J[k₀,p₀]).blowup)

local notation "π" => Iso.hom e₀ ≫ Scheme.IdealSheafData.blowupToBase (J[k₀,p₀])
local notation "ρ" => (r 2 : Fan.Ray Φ)
local notation "v" => Fan.Ray.primitiveGenerator ρ
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "center" =>
  Fan.Ray.binomialCenter ρ k₀ (m := LinearMap.toAddMonoidHom (Basis.detDualEquiv b v))
    rankTwo (b.detDualEquiv_self v) (Fan.Ray.surjective_detCharacter ρ b) c
local notation "u" => center (IsLocalRing.closedPoint k₀)
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
  Scheme.PartialMap.toRationalMap (Fan.mutationPartialMap k₀ Φ b (c : k₀) hv hPivotCone hOpp)
local notation "C'[" d' "," hd' "]" => Fan.hirzebruchPicardBasis k₀ d' 0 regΨ s hd'

include regΦ b in
private theorem plane_edge_vertex_pole {Δ : Fan i}
    (regΔ : Δ.IsRegular) (hcΔ : Δ.IsComplete) (t : Φ.IsSubdivision Δ)
    (eP : X[k₀,Δ] ≅ Plane) [eP.hom.IsOver (Spec (.of k₀))]
    {A : Scheme} [A.Over S] [IsIntegral A] [SmoothOfRelativeDimension 2 (A ↘ S)]
    (a : A ⟶ X[k₀,Φ]) [a.IsOver S] [IsDominant a] (f : A ⟶ Plane) [f.IsOver S]
    (hf : a ≫ π[t] ≫ eP.hom = f) (D : A.IdealSheafData) :
    letI : Smooth (A ↘ S) := SmoothOfRelativeDimension.smooth 2 _
    (B[Δ,hcΔ].comap eP.inv).comap f = D * ramificationIdealSheaf k₀ f →
      B[Φ,hcΦ].comap a = D * ramificationIdealSheaf k₀ a := by
  let : Nonempty Φ.cones := hcΦ.nonempty_cones
  let : Nonempty Δ.cones := hcΔ.nonempty_cones
  let : Smooth (A ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : SmoothOfRelativeDimension 2 f[Φ] :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ regΦ
  let : SmoothOfRelativeDimension 2 f[Δ] :=
    rankTwo ▸ Δ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ regΔ
  let : Smooth f[Φ] := SmoothOfRelativeDimension.smooth 2 _
  let : Smooth f[Δ] := SmoothOfRelativeDimension.smooth 2 _
  intro hpole
  let g := π[t] ≫ eP.hom
  have hBoundary : (B[Δ,hcΔ].comap eP.inv).comap eP.hom = B[Δ,hcΔ] := by
    rw [← comap_comp, eP.hom_inv_id, Scheme.IdealSheafData.comap_id]
  have hRam : ramificationIdealSheaf k₀ g = ramificationIdealSheaf k₀ π[t] := by
    dsimp only [g]
    rw [ramificationIdealSheaf_comp k₀ π[t] eP.hom 2,
      ramificationIdealSheaf_eq_top_of_isOpenImmersion k₀ eP.hom, comap_top, mul_top]
  have hB : (B[Δ,hcΔ].comap eP.inv).comap g = B[Φ,hcΦ] * ramificationIdealSheaf k₀ g := by
    rw [comap_comp, hBoundary, hRam]
    exact t.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf k₀ regΔ regΦ hcΔ rankTwo
  have hCart : ((ramificationIdealSheaf k₀ g).comap a).IsEffectiveCartier := by
    rw [hRam]
    exact (t.isEffectiveCartier_ramificationIdealSheaf k₀ regΔ regΦ hcΔ
      rankTwo).comap_of_isDominant a
  have hcomp : a ≫ g = f := hf
  apply (comap_eq_mul_ramificationIdealSheaf_comp_iff k₀ a g 2 hCart hB).mp
  exact (congrArg (B[Δ,hcΔ].comap eP.inv).comap hcomp).trans
    (hpole.trans (congrArg (D * ·) (ramificationIdealSheaf_congr k₀ hcomp).symm))

variable (j : Fin (n + 1)) (g : Y ⟶ (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀))))
  (hg : g ≫ (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀)) ↘ Spec (.of k₀)) =
    T.toBase ≫ (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀)) ↘ Spec (.of k₀)))
      (hbir : Scheme.BirationalOver g (𝟙 (Proj (homogeneousSubmodule k₀
    (Fin 3 → k₀)))))
  {Δ : Fan i} (regΔ : Δ.IsRegular) (hcΔ : Δ.IsComplete) (t : Φ.IsSubdivision Δ)
  (eP : X[k₀,Δ] ≅ (Proj (homogeneousSubmodule k₀ (Fin 3 → k₀)))) [eP.hom.IsOver (Spec (.of k₀))]

local notation "E" => Scheme.IdealSheafData.comap B[Δ,hcΔ] (Iso.inv eP)
local notation "planeMark[" T "," h "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T h fP) (Additive.ofMul (pullback g H))

include b regΔ in
omit [IsAlgClosed k₀] in
private theorem isNodeOfReducedBoundary_plane_vertex (σ : Δ.cones)
    (hσ : Nat.card (ToricRay σ.val) = 2) :
    (E).IsNodeOfReducedBoundary fP
      (eP.hom ((Δ.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀))) := by
  let : eP.inv.IsOver S := inferInstance
  have hn := Δ.isNodeOfReducedBoundary_distinguishedSection k₀ regΔ σ rankTwo hσ
  rw [← comp_over eP.inv S]
  have hx (x : X[k₀,Δ]) : eP.inv (eP.hom x) = x := by
    rw [← Scheme.Hom.comp_apply, eP.hom_inv_id]
    rfl
  exact (B[Δ,hcΔ].isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion f[Δ] eP.inv _).mpr
    (by simpa only [hx, Fan.finiteFanScheme_over k₀] using hn)

include hg hbir regΔ in
/-- At a proper high-order center on a plane edge, the opposite-vertex blowup,
mutation and ruling exchange are regular on one nodal refinement. Each partial
composite has pole ideal the reduced total transform of the original pole
divisor. The final tower has the same pole factorization in its own coordinates,
and its resolving morphism to the plane has smaller Sarkisov bidegree. -/
theorem exists_sarkisov_decrease_of_logarithmic_plane_edge
    (hπ : π = π[t] ≫ eP.hom)
    (hE : (J[k₀,p₀]).comap π = Φ.rayDivisorIdeal k₀ regΦ (r 0))
    (σ : Δ.cones) (hσ : Nat.card (ToricRay σ.val) = 2)
    (hvertex : eP.hom ((Δ.distinguishedSection (R := k₀) σ) (IsLocalRing.closedPoint k₀)) = p₀)
    (hj : hT.baseCenter j = π u)
    (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (hhigh : let w := planeMark[T,hT,g]; degree w.1 < 3 * (-w.2 j))
    (D : Y.IdealSheafData) (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ T.toBase ≫ fP))
    (hpole : (E).comap T.toBase = D * hT.ramificationIdealSheafToBase k₀) :
    letI : Nonempty (Φ).cones := (hcΦ).nonempty_cones
    letI : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
    letI : SmoothOfRelativeDimension 2 f[Ψ] :=
      Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d f[Ψ]) rankTwo)
      ((Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ regΨ)
    ∃ (A : Scheme) (q : A ⟶ Y) (a : A ⟶ X[k₀,Φ])
      (d' : Basis (Fin 2) ℤ N)
      (hd' : (fun l ↦ (s l).primitiveGenerator) = ![d' 0, d' 1, -d' 0, (0 : ℤ) • d' 0 - d' 1])
      (m : ℕ) (Z : Scheme) (U : BlowupTower X[k₀,Ψ] m Z) (hU : IsClosedPointTower X[k₀,Ψ] U)
      (e : A ≅ Z) (p : A ⟶ X[k₀,Ψ]) (_ : IsIntegral A) (_ : IsDominant a)
      (k : ℕ) (W : Scheme) (R : BlowupTower Y k W) (e₁ : A ≅ W)
      (_ : IsNodalBoundaryTower D (T.toBase ≫ fP) (𝟙 Y) R),
      let τ := ((Fan.quadricRulingExchange d' regΨ hcΨ s hd').toFanHom.finiteFanSchemeHom k₀)
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
        B[Φ,hcΦ].comap a = D' * ramificationIdealSheaf k₀ a ∧
        B[Ψ,hcΨ].comap p = D' * ramificationIdealSheaf k₀ p ∧
        B[Ψ,hcΨ].comap (p ≫ τ) = D' * ramificationIdealSheaf k₀ (p ≫ τ) ∧
        B[Ψ,hcΨ].comap U.toBase = D'.comap e.inv * hU.ramificationIdealSheafToBase k₀ ∧
        g' ≫ fP = U.toBase ≫ f[Ψ] ∧ Scheme.BirationalOver g' (𝟙 Plane) ∧
        let w := planeMark[T,hT,g]
        let y := (U.picardMarking hU f[Ψ]).symm (Additive.ofMul (pullback g' H))
        (C'[d',hd']).repr y.1 1 = degree w.1 + w.2 j ∧
        0 < (C'[d',hd']).repr y.1 1 ∧
        hirzebruchSarkisovBidegree ((C'[d',hd']).repr y.1 1).toNat (∑ l, (-y.2 l).toNat) <
          planeSarkisovBidegree (degree w.1).toNat (∑ l, (-w.2 l).toNat) := by
  let : Nonempty Φ.cones := hcΦ.nonempty_cones
  let : Nonempty (Ψ).cones := (hcΨ).nonempty_cones
  let : SmoothOfRelativeDimension 2 f[Φ] :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ regΦ
  let : SmoothOfRelativeDimension 2 f[Ψ] :=
    Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d f[Ψ]) rankTwo)
      ((Ψ).smoothOfRelativeDimension_finiteFanSchemeToSpec k₀ regΨ)
  have hπOver : π ≫ fP = f[Φ] := by
    rw [hπ, Category.assoc, comp_over eP.hom S, comp_over π[t] S]
  have hsection : ((Δ.distinguishedSection (R := k₀) σ) ≫ eP.hom) ≫ fP = 𝟙 S := by
    rw [Category.assoc, comp_over eP.hom S, Fan.finiteFanScheme_over k₀,
      Fan.distinguishedSection_comp_finiteFanSchemeToSpec]
  have hp₀ : IsClosed ({p₀} : Set Plane) := by
    have hpoint := (Scheme.Hom.comp_apply ((Δ.distinguishedSection (R := k₀) σ)) eP.hom
      (IsLocalRing.closedPoint k₀)).trans hvertex
    exact hpoint ▸ isClosed_singleton_of_section hsection
  obtain ⟨A, q, k', R', hR', d', hd', m, Z, U, hU, e, p, hI, hdom, hqIso, hqBlowup,
    habase, hmut, hτ, hg', hb', hdegree, hpos, hlt⟩ :=
    hT.exists_sarkisov_decrease_of_plane_edge k₀ j g hg hbir regΦ hcΦ b r hr c hp₀ e₀
      hπOver hE hj hfirst hhigh
  have hnode := isNodeOfReducedBoundary_plane_vertex k₀ b regΔ hcΔ eP σ hσ
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
  have hBasePole := comap_eq_mul_ramificationIdealSheaf_comp k₀ q T.toBase 2
    ((hT.ramificationIdealSheafToBase_def k₀) ▸ hpole) hqPole
  have habase' : a ≫ π[t] ≫ eP.hom = q ≫ T.toBase := hπ ▸ habase
  have haPole := plane_edge_vertex_pole k₀ regΦ hcΦ b regΔ hcΔ t eP a _ habase' D' hBasePole
  obtain ⟨hp, hiff⟩ := (ρ).mutation_resolution_poleIdeal_iff k₀ b hOpp c hR' regΦ hcΦ p D' hmut
  have hpPole := hiff.mp ((hR'.ramificationIdealSheafToBase_def k₀).symm ▸ haPole)
  let := hp
  let F := Fan.quadricRulingExchange d' regΨ hcΨ s hd'
  let τ := (F.toFanHom.finiteFanSchemeHom k₀)
  have hτPole := comap_eq_mul_ramificationIdealSheaf_comp k₀ p τ 2 (D := B[Ψ,hcΨ])
    (P := B[Ψ,hcΨ]) (by
      rw [ramificationIdealSheaf_eq_top_of_isOpenImmersion, mul_top]
      exact F.comap_toricBoundaryIdeal_finiteFanSchemeHom k₀ _ _) hpPole
  have hUPole := congrArg (fun I : A.IdealSheafData ↦ I.comap e.inv) hτPole
  rw [comap_mul, ← hU.comap_ramificationIdealSheafToBase k₀ e hτ,
    ← comap_comp, ← hτ, e.inv_hom_id_assoc, ← comap_comp, e.inv_hom_id,
    Scheme.IdealSheafData.comap_id] at hUPole
  exact ⟨A, q, a, d', hd', m, Z, U, hU, e, p, hI, hdom, k, W, R, e₁, hR,
    hA, ha, hp, hk, he₁, habase', hmut, hτ, haPole, hpPole, hτPole, hUPole, hg', hb',
    hdegree, hpos, hlt⟩

end Edge

end QPainleve.BlowupTower.IsClosedPointTower
