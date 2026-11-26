/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Period.Surjectivity
public import QPainleve.Geometry.Toric.Fan.TorusAction.Alignment

/-!
# Aligning contracted toric presentations by their periods

The period formula of [Gross, Hacking and Keel, Proposition 2.9](
https://arxiv.org/html/1211.6367v5#S2) detects equality of center characters on
the charge kernel. If the same rays survive the chosen contractions, equal
ordered periods therefore give an isomorphism of pairs compatible with the
entire Picard marking and with rational X evaluation.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry Scheme.IdealSheafData
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)
  (c d : Multiplicative (Fin n → ℤ) →* ℂˣ)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "C" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ inferInstance)
local notation "center" a:arg => (fun j : Fin n ↦ a (ofAdd (Pi.single j 1)))
local notation "M" a:arg => internalBlowupTower b s (center a)
local notation "π" a:arg => toBase (WithBoundary.toTower (Sigma.snd (M a)))
local notation "strict[" a "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd (M a)))
local notation "prime[" a "]" => internalBlowupBoundaryPrimeEquiv hΦ b s (center a)
local notation "base" => Φ.algebraicRealizationStructureMap

variable [PrestableFamily ((Φ.boundaryIdeal inferInstance).subscheme ↘ Spec (.of ℂ))]
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ Spec (.of ℂ))]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ))))]
  {α : Type*} {p₀ : α → ((Φ.boundaryIdeal inferInstance).subscheme ↘ S).smoothLocus}
  {a : ℕ} [NeZero a] (A : NodalCycleNumbering p₀ a)

variable {X X' Y Y' : Scheme} [IsIntegral X] [IsIntegral X']
  {f : X ⟶ S} {g : X' ⟶ S} [SmoothOfRelativeDimension 2 f] [SmoothOfRelativeDimension 2 g]
  [QuasiCompact f] [QuasiCompact g]
  {D : X.IdealSheafData} {D' : X'.IdealSheafData} [IsReduced D.subscheme] [IsReduced D'.subscheme]
  {m m' : ℕ} {T : BlowupTower X m Y} {U : BlowupTower X' m' Y'}

local notation "p[" a "]" => (Iso.inv a ≫ toBase T)
local notation "q[" a "]" => (Iso.inv a ≫ toBase U)

/-- Equal ordered periods in the positive toric orientation give a translating
isomorphism of the contracted pairs when the surviving ray labels agree. It identifies
the full marked Picard pullbacks and commutes with the fixed-center X evaluations.
The centers can repeat, and the charge image can have any rank. -/
theorem exists_iso_of_eq_orderedBoundaryPeriod
    (r : ZMod a ≃ Φ.Ray)
    (hcomp : ∀ j, (C).dualGraphVertexEquiv p₀ (A.vertex j) =
      Φ.boundaryNormalizationComponentEquiv hΦ (r j))
    (hdet : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ ∧
      (Φ.boundaryIdeal inferInstance).subschemeι ((C).dualGraphEdgeEquiv p₀ (A.edge j)).val =
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hT : IsNodalBoundaryTower D f (𝟙 X) T) (hU : IsNodalBoundaryTower D' g (𝟙 X') U)
    (e : Y ≅ (M c).1) (e' : Y' ≅ (M d).1)
    (hc : p[e] ≫ f = π c ≫ base) (hd : q[e'] ≫ g = π d ≫ base)
    (hD : (D.comap p[e]).support = strict[c].support)
    (hD' : (D'.comap q[e']).support = strict[d].support)
    (hkeep : ∀ ρ : Φ.Ray, p[e] (prime[c] ρ).val ∈ D.boundaryPrimes ↔
      q[e'] (prime[d] ρ).val ∈ D'.boundaryPrimes)
    (hperiod : orderedBoundaryPeriod hΦ b s A (center c) =
      orderedBoundaryPeriod hΦ b s A (center d)) :
    ∃ j : X ≅ X', j.hom ≫ g = f ∧ D'.comap j.hom = D ∧
      Nonempty (ContractedToricTranslation b s p[e] q[e'] j) := by
  exact exists_iso_of_eq_center_character hΦ b s c d hT hU e e' hc hd hD hD' hkeep
    ((orderedBoundaryPeriod_eq_iff hΦ b s A r hcomp hdet hnodes (center c) (center d)).mp hperiod)

end TauCeti.Toric.Fan
