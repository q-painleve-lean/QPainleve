/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined
public import QPainleve.Geometry.Toric.Fan.Boundary.Contraction
public import QPainleve.Geometry.Toric.Fan.Evaluation.Contraction
public import QPainleve.Geometry.Toric.Fan.Mutation.Word

import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Tropical boundary transport on contracted pairs

The evaluation square of an isomorphism of contracted pairs compares its boundary
action with the toric valuation transport of the word. At fixed centers the two
evaluations may be nondominant, so the comparison uses their generic values on
the domain of the word. The target presentation may be in a different lattice
from the fan constructed by `Fan.exists_toric_boundary_valuation_transport`.

The boundary transport uses the elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module Multiplicative Quiver
open QPainleve.BlowupTower QPainleve.Cluster TauCeti.AlgebraicGeometry TauCeti.LaurentRing

namespace TauCeti.Toric.Fan

variable {N V N' V' : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [Nonempty Φ.cones] [Nonempty Ψ.cones] {r : ℕ}
  (b : Basis (Fin 2) ℤ N) (b' : Basis (Fin 2) ℤ N')
  (s : Fin r → Φ.Ray) (t : Fin r → Ψ.Ray) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular)
  (c d : Multiplicative (Fin r → ℤ) →* ℂˣ)

local notation "center" a:arg => (fun j : Fin r ↦ a (ofAdd (Pi.single j 1)))
local notation "π[" a "," s "," c "]" =>
  toBase (WithBoundary.toTower (Sigma.snd (internalBlowupTower a s (center c))))
local notation "K(" Φ ")" => Scheme.functionField (Fan.algebraicRealization Φ)
local notation "trop" => Paths.lift (tropicalPrefunctor (A := ℤ) (Fin r))

variable {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
  (p : (internalBlowupTower b s (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))).1 ⟶ X)
  (q : (internalBlowupTower b' t (fun j : Fin r ↦ d (ofAdd (Pi.single j 1)))).1 ⟶ Y)
  [IsModification p] [IsModification q]
  {B C : SkewExchangeMatrix (Fin r)} (w : Word B C) (e : X ≅ Y)

local notation "E₀" => contractedXEvaluation b s c hΦ p
local notation "E₁" => contractedXEvaluation b' t d hΨ q
local notation "wordMap" => Path.xRationalMap ℂ w

local notation "evaluationSquare" =>
  (∃ h : Scheme.RationalMap.fromFunctionField E₀
      (IsLocalRing.closedPoint (Scheme.functionField X)) ∈ Scheme.RationalMap.domain wordMap,
    Scheme.RationalMap.compOfDefined E₀ wordMap h =
      Scheme.RationalMap.comp (Scheme.Hom.toRationalMap (Iso.hom e)) E₁)

/-- Compare the coordinate pullbacks through a generic lift of the word's source evaluation. -/
private theorem functionFieldMap_contracted_coordinate {Ω : Fan i} [Nonempty Ω.cones]
    (heval : evaluationSquare) (bΩ : Basis (Fin 2) ℤ N)
    (u : Fin r → Ω.Ray) (a : Multiplicative (Fin r → ℤ) →* ℂˣ)
    (g : K(Ω) ≃ₐ[ℂ] K(Φ)) (l : Spec K(Φ) ⟶ (wordMap).toPartialMap.domain)
    (hl : l ≫ (wordMap).toPartialMap.domain.ι = (Φ.xEvaluation b s c).fromFunctionField)
    (hl' : l ≫ (wordMap).toPartialMap.hom =
      Spec.map (CommRingCat.ofHom g.toRingEquiv.toRingHom) ≫
        (Ω.xEvaluation bΩ u a).fromFunctionField) (j : Fin r) :
    let := isIntegral_internalBlowupTower b s (center c) hΦ
    let := isIntegral_internalBlowupTower b' t (center d) hΨ
    let := isModification_internalBlowupTower_toBase b s (center c) hΦ
    let := isModification_internalBlowupTower_toBase b' t (center d) hΨ
    let := p.isIso_functionFieldMap_of_isModification
    let := q.isIso_functionFieldMap_of_isModification
    e.hom.functionFieldMap (inv q.functionFieldMap
      ((π[b',t,d]).functionFieldMap (Ψ.xEval b' t d (LaurentRing.X j)))) =
      inv p.functionFieldMap
        ((π[b,s,c]).functionFieldMap (g (Ω.xEval bΩ u a (LaurentRing.X j)))) := by
  have := isIntegral_internalBlowupTower b s (center c) hΦ
  have := isIntegral_internalBlowupTower b' t (center d) hΨ
  have := isModification_internalBlowupTower_toBase b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase b' t (center d) hΨ
  have := p.isIso_functionFieldMap_of_isModification
  have := q.isIso_functionFieldMap_of_isModification
  -- Transport the toric generic lift to the function field of the contracted source.
  let m := (π[b,s,c]).functionFieldMap ≫ inv p.functionFieldMap
  let lX := Spec.map m ≫ l
  have hlX : lX ≫ (wordMap).toPartialMap.domain.ι = (E₀).fromFunctionField := by
    simp only [lX, Category.assoc, hl, fromFunctionField_xEvaluation,
      fromFunctionField_contractedXEvaluation, m, ← Spec.map_comp]
  obtain ⟨h, hsquare⟩ := heval
  have hgeneric := congrArg Scheme.RationalMap.fromFunctionField hsquare
  rw [Scheme.RationalMap.fromFunctionField_compOfDefined _ _ h lX hlX,
    Scheme.RationalMap.fromFunctionField_comp, Scheme.Hom.functionFieldMap_toRationalMap,
    fromFunctionField_contractedXEvaluation] at hgeneric
  simp only [lX, Category.assoc, hl', fromFunctionField_xEvaluation,
    ← Spec.map_comp, Spec.map_inj] at hgeneric
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv, m] using
    ConcreteCategory.congr_hom hgeneric.symm (LaurentRing.X j : LaurentRing ℂ (Fin r))

variable [IsNormalScheme X] [IsNormalScheme Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  {D : X.IdealSheafData} {E : Y.IdealSheafData}
  (hp : (D.comap p).support =
    (internalBlowupTower b s (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))).2.boundaryι.ker.support)
  (hq : (E.comap q).support =
    (internalBlowupTower b' t (fun j : Fin r ↦ d (ofAdd (Pi.single j 1)))).2.boundaryι.ker.support)
  (hcΦ : Φ.IsComplete)
  (hB : B.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s))

local notation "ρ" => contractedBoundaryRayEmbedding hΦ b s (center c) p hp
local notation "τ" => contractedBoundaryRayEmbedding hΨ b' t (center d) q hq

include hcΦ hB hp hq in
/-- Under the fixed-center evaluation square for a signed word, the orders
along an image boundary prime are the tropical word applied to the orders at its
source prime. The result holds for charges of any rank. -/
theorem rayBoundaryOrders_eq_tropical_of_comp_contractedXEvaluation
    (heval : evaluationSquare) (x : D.boundaryPrimes) (y : E.boundaryPrimes)
    (hy : e.hom x.val = y.val) :
    rayBoundaryOrders b' t (τ y) =
      DFunLike.coe (F := Equiv.Perm (Fin r → ℤ)) ((trop).map w) (rayBoundaryOrders b s (ρ x)) := by
  let P := rayChargeSeed b s hB
  let bΩ := if Even w.inversionCount then b else b.reindex (Equiv.swap 0 1)
  obtain ⟨Ω, hΩ, hΩc, u, f, -, -, horders, hfield⟩ :=
    exists_toric_boundary_valuation_transport b w P hΦ hcΦ s
      (rayChargeSeed_form _ _ _) (rayChargeSeed_charge _ _ _)
  let : Nonempty Ω.cones := hΩc.nonempty_cones
  obtain ⟨g, hg, he⟩ := hfield
  obtain ⟨l, hl, hl'⟩ := he c
  have := isIntegral_internalBlowupTower b s (center c) hΦ
  have := isIntegral_internalBlowupTower b' t (center d) hΨ
  have := isModification_internalBlowupTower_toBase b s (center c) hΦ
  have := isModification_internalBlowupTower_toBase b' t (center d) hΨ
  have := p.isIso_functionFieldMap_of_isModification
  have := q.isIso_functionFieldMap_of_isModification
  rw [← horders]
  ext j
  rw [← ord_contracted_toric_boundary_chargeCharacter hΨ b' t (center d) q hq,
    ← hy, ← TauCeti.AlgebraicGeometry.Scheme.ord_functionFieldMap e.hom]
  simp only [← xEval_X]
  rw [functionFieldMap_contracted_coordinate b b' s t hΦ hΨ c d p q w e heval bΩ _ _ (g c)
      l hl hl' j,
    ord_contracted_toric_boundary hΦ b s (center c) p hp, hg,
    xEval_X, ord_rayBoundaryPoint_chargeCharacter]

include hcΦ hB hp hq in
/-- For finite-index target charges, searching the numbered target boundary with
the tropical word's output returns precisely the label of the image prime. -/
theorem boundaryRayOfOrders_tropical_word (heval : evaluationSquare)
    {n : ℕ} (boundary : Fin n ↪ E.boundaryPrimes)
    (hindex : (rayChargeMap t).range.toAddSubgroup.index ≠ 0)
    (hboundary : (E.comap e.hom).support = D.support) (x : D.boundaryPrimes) (j : Fin n) :
    boundaryRayOfOrders b' t (boundary.trans τ)
      (DFunLike.coe (F := Equiv.Perm (Fin r → ℤ)) ((trop).map w) (rayBoundaryOrders b s (ρ x))) =
        some j ↔
      e.hom x.val = (boundary j).val := by
  have hx : x.val ∈ (E.comap e.hom).boundaryPrimes :=
    (Scheme.IdealSheafData.boundaryPrimes_eq_of_support_eq hboundary).symm ▸ x.property
  let y := E.boundaryPrimesEquivOfIso e ⟨x.val, hx⟩
  have hy : y.val = e.hom x.val := E.boundaryPrimesEquivOfIso_apply_val e _
  rw [boundaryRayOfOrders_eq_some_iff _ _ _ _ hindex, Function.Embedding.trans_apply,
    ← rayBoundaryOrders_eq_tropical_of_comp_contractedXEvaluation b b' s t hΦ hΨ c d p q w e
      hp hq hcΦ hB heval x y hy.symm, ← hy]
  exact ⟨fun h ↦ congrArg Subtype.val
    ((τ).injective (rayBoundaryOrders_injective b' t hindex h)).symm,
    fun h ↦ congrArg (fun z ↦ rayBoundaryOrders b' t (τ z)) (Subtype.ext h).symm⟩

end TauCeti.Toric.Fan
