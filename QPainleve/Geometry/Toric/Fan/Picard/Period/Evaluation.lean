/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Period.Comparison
public import QPainleve.Geometry.Toric.Fan.TorusAction.MarkedEvaluation

import QPainleve.Geometry.Toric.Fan.Picard.Period.Presentation
import QPainleve.Geometry.Toric.Fan.Picard.Period.Surjectivity

/-!
# Fixed-center X evaluation from marked pullbacks

For two contractions of the same ordered toric presentation, a pair isomorphism
that identifies their marked Picard classes and ordered surviving boundary
intertwines their rational X evaluations. The periods compare the center
characters on the charge kernel. The comparison then uses the aligned-center
evaluation theorem, which allows repeated internal centers.

The period and automorphism formulas are those of Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*,
[Propositions 2.6 and 2.9](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {r : ℕ}
  (b : Module.Basis (Fin 2) ℤ N) (s : Fin r → Φ.Ray) (hΦ : Φ.IsRegular)
  (c d : Multiplicative (Fin r → ℤ) →* ℂˣ)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "center" t:arg => (fun j : Fin r ↦ t (ofAdd (Pi.single j 1)))
local notation "J[" t "]" =>
  (fun j : Fin r ↦ Ray.internalCenter b (s j) (t (ofAdd (Pi.single j 1))))
local notation "M" t:arg => internalBlowupTower b s (center t)
local notation "π" t:arg => toBase (WithBoundary.toTower (Sigma.snd (M t)))
local notation "ι" t:arg => WithBoundary.boundaryι (Sigma.snd (M t))
local notation "mark" t:arg => internalBlowupPicardMarking b s (center t) hΦ
local notation "prime" t:arg => internalBlowupBoundaryPrimeEquiv hΦ b s (center t)
local notation "Dtor" => Scheme.IdealSheafData.subscheme (Φ.boundaryIdeal h₀)

local notation "base" => Φ.algebraicRealizationStructureMap
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "smoothBase" => cast (congrArg (fun n ↦ SmoothOfRelativeDimension n base) rankTwo)
    (Fan.smoothOfRelativeDimension_algebraicRealizationStructureMap Φ hΦ)

variable {X Y W Z : Scheme} [X.Over S] [Y.Over S] [IsIntegral X] [IsIntegral Y]
  [X.IsProjectiveOver ℂ] [Y.IsProjectiveOver ℂ] [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (Y ↘ S)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ Y)]
  {D : X.IdealSheafData} {E : Y.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ S)] [PrestableFamily (E.subscheme ↘ S)]
  [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)]
  {l l' : ℕ} {P : BlowupTower X l W} {Q : BlowupTower Y l' Z}
  (hP : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) P)
  (hQ : IsNodalBoundaryTower E (Y ↘ S) (𝟙 Y) Q)
  (e : W ≅ (internalBlowupTower b s (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))).1)
  (e' : Z ≅ (internalBlowupTower b s (fun j : Fin r ↦ d (ofAdd (Pi.single j 1)))).1)

local notation "p" => (Iso.inv e ≫ toBase P)
local notation "q" => (Iso.inv e' ≫ toBase Q)

variable {n m : ℕ} [NeZero n] [NeZero m] {α β γ : Type*}
  {a : α → (D.subscheme ↘ S).smoothLocus} {a' : β → (E.subscheme ↘ S).smoothLocus}
  {t : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  (A : NodalCycleNumbering a n) (B : NodalCycleNumbering a' n) (C : NodalCycleNumbering t m)

/-- A pair isomorphism with matching Picard coordinates intertwines the X evaluations if
its boundary action is the rotation prescribed by the surviving rays. Both contractions
use the orientation induced by the same ordered toric boundary. The charge image may have
any rank. -/
theorem comp_contractedXEvaluation_eq_of_matching_markings
    (hc : Φ.IsComplete)
    (hp : p ≫ (X ↘ S) = π c ≫ base) (hq : q ≫ (Y ↘ S) = π d ≫ base)
    (hD : ((D.comap P.toBase).comap e.inv).support = (ι c).ker.support)
    (hE : ((E.comap Q.toBase).comap e'.inv).support = (ι d).ker.support)
    (u : ZMod m ≃ Φ.Ray)
    (hvertices : ∀ j, (Dtor).dualGraphVertexEquiv t (C.vertex j) =
      Φ.boundaryNormalizationComponentEquiv hΦ (u j))
    (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
      (Φ.boundaryIdeal h₀).subschemeι ((Dtor).dualGraphEdgeEquiv t (C.edge j)).val =
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hCartierD : D.IsEffectiveCartier) (hCartierE : E.IsEffectiveCartier)
    (gD : ∀ v : irreducibleComponents (D.subscheme.singularLocus ℂ).blowup,
      (D.subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (gE : ∀ v : irreducibleComponents (E.subscheme.singularLocus ℂ).blowup,
      (E.subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (f : Dtor ⟶ D.subscheme) (g : Dtor ⟶ E.subscheme) [f.IsOver S] [g.IsOver S]
    (hf : f ≫ D.subschemeι = ι c ≫ p) (hg : g ≫ E.subschemeι = ι d ≫ q)
    (hfs : f.IsOrientedCycleSubdivision C A) (hgs : g.IsOrientedCycleSubdivision C B)
    (hkeep : ∀ ρ : Φ.Ray, p ((prime c) ρ).val ∈ D.boundaryPrimes ↔
      q ((prime d) ρ).val ∈ E.boundaryPrimes)
    (v : X ≅ Y) [v.hom.IsOver S] (vB : D.subscheme ≅ E.subscheme) [vB.hom.IsOver S]
    (hv : vB.hom ≫ E.subschemeι = D.subschemeι ≫ v.hom)
    (hPic : ∀ L : LineBundleClass Y,
      (mark c).symm (Additive.ofMul (pullback p (pullback v.hom L))) =
        (mark d).symm (Additive.ofMul (pullback q L)))
    (j : ZMod n) (hact : vB.boundaryCycleAction A B = DihedralGroup.r j)
    (x : D.boundaryPrimes) (y : E.boundaryPrimes)
    (hx : x.val = D.subschemeι (A.componentGenericPoint 0))
    (hy : y.val = E.subschemeι (B.componentGenericPoint j))
    (ρ : Φ.Ray) (hxρ : p ((prime c) ρ).val = x.val) (hyρ : q ((prime d) ρ).val = y.val) :
    let : IsModification P.toBase :=
      hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
    let : IsModification Q.toBase :=
      hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Y ↘ S)
    v.hom.toRationalMap.comp (contractedXEvaluation b s d hΦ q) =
      contractedXEvaluation b s c hΦ p := by
  let : IsModification P.toBase :=
    hP.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  let : IsModification Q.toBase :=
    hQ.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Y ↘ S)
  -- Read the same marked pullback in the presentations used by the period maps.
  obtain ⟨eD, heD, hDs, hfD, hmarkD⟩ := exists_period_presentation b s hΦ c e hp hD f hf
  obtain ⟨eE, heE, hEs, hgE, hmarkE⟩ := exists_period_presentation b s hΦ d e' hq hE g hg
  have hmark := markedBoundaryPeriod_eq_of_pullback_marking hΦ b s hP hQ eD eE heD heE hDs hEs
    hCartierD hCartierE gD gE A B vB hv.symm
    (fun L ↦ (hmarkD (pullback v.hom L)).trans ((hPic L).trans (hmarkE L).symm))
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) := by
    rw [algebraicRealization_over]
    exact smoothBase
  let : ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))).IsPerfPair :=
    isPerfPair_internal_markedForm hΦ rankTwo s
      (fun j ↦ (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom)
      (fun j ↦ b.detDualEquiv_self (s j).primitiveGenerator)
      (fun j ↦ (s j).surjective_detCharacter b) (center c) (J[c])
      (fun j ↦ (s j).internalCenter_val b (c (ofAdd (Pi.single j 1)))) hP eD heD
  have hperiodD := markedBoundaryPeriod_eq_orderedBoundaryPeriod hΦ b s C hP eD heD hDs
    hCartierD gD A (hfD ▸ hfs)
  have hperiodE := markedBoundaryPeriod_eq_orderedBoundaryPeriod hΦ b s C hQ eE heE hEs
    hCartierE gE B (hgE ▸ hgs)
  -- Both projections preserve branch order, and the comparison rotates the original cycle.
  have hperiod :
      orderedBoundaryPeriod hΦ b s C (center c) = orderedBoundaryPeriod hΦ b s C (center d) := by
    have hsign : (1 : ℤˣ) ≠ -1 := by decide
    rw [hact, DihedralGroup.cycleOrientationSign_r, ite_eq_right hsign, hperiodD, hperiodE] at hmark
    exact hmark
  have hcenters := (orderedBoundaryPeriod_eq_iff hΦ b s C u hvertices hdet hnodes _ _).mp hperiod
  exact comp_contractedXEvaluation_eq_of_eq_center_character b s hΦ c d hc hCartierE
    hP hQ e e' hp hq (by simpa only [comap_comp] using hD) (by simpa only [comap_comp] using hE)
    hkeep hcenters A B C f g hf hg hfs hgs v vB hv hPic j hact x y hx hy ρ hxρ hyρ

end TauCeti.Toric.Fan
