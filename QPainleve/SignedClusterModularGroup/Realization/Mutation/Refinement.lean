/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Refinement
public import QPainleve.SignedClusterModularGroup.Realization.Refinement.Valuation

import QPainleve.Geometry.Toric.Fan.StarSubdivision.RayInsertion

/-!
# Preparing marked toric families for mutation

In a complete fan, insert the opposite of the pivot ray by regular subdivision.
The ordered internal models on the refined fan still contract to the same
marked surfaces. Their boundary rays above the numbered components are the
lifts of the original rays, and their charge map is the original charge map.
The construction uses `Fan.Ray.exists_regular_subdivision_containing_opposite` and
`ContractedToricFiber.exists_subdivision_family`.
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative PointedCone
open QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan

namespace QPainleve.SignedClusterModularGroup.ContractedToricFiber

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {b : Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "S" => Spec (CommRingCat.of k₀)
local notation "D[" coeff "," Φ "," h "]" => Scheme.IdealSheafData.subscheme
  (Fan.toricBoundaryIdeal coeff Φ h)
local notation "Dₘ[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "Pic[" coeff "," Φ "," r "]" =>
  Additive (LineBundleClass (Fan.finiteFanScheme coeff Φ)) × (Fin r → ℤ)
local notation "centers" c:arg => (fun j : Fin _ ↦ c (ofAdd (Pi.single j 1)))
local notation "model[" b "," s "," c "]" => Sigma.fst (Fan.internalBlowupTower k₀ b s (centers c))

variable [PrestableFamily (D[k₀,Φ,hΦ₀] ↘ Spec (.of k₀))]
  {α : Type*} {a : α → (D[k₀,Φ,hΦ₀] ↘ Spec (.of k₀)).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m} {o : ZMod m} {J : L →ₗ[ℤ] Pic[k₀,Φ,r]}
  {C : Type*} {χ : C → Multiplicative (Fin r → ℤ) →* k₀ˣ}
  {P : C → MarkedSurface k₀ n B (Spec (CommRingCat.of (LaurentRing k₀ (Fin r))))}

/-- A single regular refinement prepares the pivot for mutation throughout the
center family. The refined contractions have the original marked surfaces as
targets, with the refined Picard inclusion and the lifts of exactly the original
numbered rays. The existing order of the centers is retained, including repeated
centers. -/
theorem exists_subdivision_for_pivot (hc : Φ.IsComplete) (k : Fin r)
    (p : ∀ t, ContractedToricFiber b s hΦ T o J (χ t) (P t))
    (hP : ∀ t, ∃ (Y : Scheme) (j : ℕ) (R : BlowupTower (P t).surface j Y)
      (e : Y ≅ model[b,s,χ t]),
      IsNodalBoundaryTower Dₘ[P t] ((P t).surface ↘ S) (𝟙 _) R ∧
        (p t).projection = e.inv ≫ R.toBase) :
    ∃ (Ψ : Fan i) (h : Ψ.IsSubdivision Φ) (hΨ : Ψ.IsRegular) (hc' : Ψ.IsComplete),
      letI := hc'.nonempty_cones
      hull ℝ {i (-(h.liftRay (s k)).primitiveGenerator)} ∈ Ψ.cones ∧
      rayChargeMap (h.liftRay ∘ s) = rayChargeMap s ∧
      ∃ (hpre : PrestableFamily (D[k₀,Ψ,hc'.nonempty_cones] ↘ S)) (l : ℕ) (_ : NeZero l),
        letI := hpre
        ∃ (U : Scheme.NodalCycleNumbering (Empty.elim : Empty → (D[k₀,Ψ,hc'.nonempty_cones] ↘
          S).smoothLocus) l) (o' : ZMod l),
          ∀ t, ∃ (q : ContractedToricFiber b (h.liftRay ∘ s) hΨ U o'
            ((h.internalBlowupPicardPullback k₀).comp J) (χ t) (P t))
            (Y : Scheme) (j : ℕ) (R : BlowupTower (P t).surface j Y)
            (e : Y ≅ model[b,h.liftRay ∘ s,χ t]),
            IsNodalBoundaryTower Dₘ[P t] ((P t).surface ↘ S) (𝟙 _) R ∧
              q.projection = e.inv ≫ R.toBase ∧
              q.boundaryMap = h.boundaryMap k₀ hc'.nonempty_cones hΦ₀ ≫ (p t).boundaryMap ∧
              ∀ hD : Dₘ[P t].IsEffectiveCartier, ∀ j : ZMod n,
                q.numberedBoundaryRays hD j = h.liftRay ((p t).numberedBoundaryRays hD j) := by
  have hN := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨Ψ, h, hΨ, hc', hopp⟩ := (s k).exists_regular_subdivision_containing_opposite hΦ hc hN
  let : Nonempty Ψ.cones := hc'.nonempty_cones
  refine ⟨Ψ, h, hΨ, hc', hopp, h.rayChargeMap_liftRay s, ?_⟩
  obtain ⟨hpre, l, hl, hdata⟩ := exists_subdivision_family (δ := Empty) h χ P p hΨ hc hP
  let : PrestableFamily (D[k₀,Ψ,hc'.nonempty_cones] ↘ S) := hpre
  obtain ⟨U, o', _, _, hq⟩ := hdata Empty.elim
  refine ⟨hpre, l, hl, U, o', fun t ↦ ?_⟩
  obtain ⟨q, Y, j, R, e, hR, hproj, hboundary⟩ := hq t
  exact ⟨q, Y, j, R, e, hR, hproj, hboundary,
    (p t).numberedBoundaryRays_subdivision h q hboundary⟩

end QPainleve.SignedClusterModularGroup.ContractedToricFiber
