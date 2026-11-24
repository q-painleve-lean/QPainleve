/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Period.Reconstruction

import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Surviving
import QPainleve.Geometry.Toric.Fan.Picard.Period.Presentation

/-!
# Reconstruction from signed boundary periods

In common toric Picard coordinates, the signed period equation on the original
boundaries gives equality of the periods on the positively numbered toric
boundary. The matching marked pullbacks also identify the contracted rays.
Together these comparisons let the translating isomorphism realizing the
prescribed Picard map descend to the original pairs.

See [Gross, Hacking and Keel, Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2)
for reconstruction of a pair isomorphism from its period.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve QPainleve.BlowupTower
open TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData
open Scheme (NodalCycleNumbering)

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones] {r : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin r → Φ.Ray)
  (c d : Multiplicative (Fin r → ℤ) →* ℂˣ)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Btor" => Scheme.IdealSheafData.subscheme (Φ.boundaryIdeal h₀)
local notation "center" a:arg => (fun j : Fin r ↦ a (ofAdd (Pi.single j 1)))
local notation "M" a:arg => internalBlowupTower b s (center a)
local notation "π" a:arg => toBase (WithBoundary.toTower (Sigma.snd (M a)))
local notation "ι" a:arg => WithBoundary.boundaryι (Sigma.snd (M a))
local notation "mark" a:arg => internalBlowupPicardMarking b s (center a) hΦ
local notation "prime[" a "]" => internalBlowupBoundaryPrimeEquiv hΦ b s (center a)
local notation "base" => Φ.algebraicRealizationStructureMap

variable {X Y W Z : Scheme} [X.Over S] [Y.Over S]
  {D : X.IdealSheafData} {E : Y.IdealSheafData}
  {l l' : ℕ} {T : BlowupTower X l W} {U : BlowupTower Y l' Z}
  (e : W ≅ (internalBlowupTower b s (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))).1)
  (e' : Z ≅ (internalBlowupTower b s (fun j : Fin r ↦ d (ofAdd (Pi.single j 1)))).1)

local notation "p" => (Iso.inv e ≫ toBase T)
local notation "q" => (Iso.inv e' ≫ toBase U)

variable [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)] [PrestableFamily (D.subscheme ↘ S)]
  [PrestableFamily (E.subscheme ↘ S)]
  {n m : ℕ} [NeZero n] [NeZero m] {α β γ : Type*}
  {a₀ : α → (D.subscheme ↘ S).smoothLocus} {a₁ : β → (E.subscheme ↘ S).smoothLocus}
  {aT : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  (A : NodalCycleNumbering a₀ n) (B : NodalCycleNumbering a₁ n) (C : NodalCycleNumbering aT m)

variable [IsIntegral X] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (Y ↘ S)]
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]

variable [X.IsProjectiveOver ℂ] [Y.IsProjectiveOver ℂ]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ X)]
  [LinearMap.IsPerfPair (Chow.intersectionBilinForm ℂ Y)]

local notation "J[" t "]" =>
  (fun j : Fin r ↦ Ray.internalCenter b (s j) (t (ofAdd (Pi.single j 1))))

/-- Signed period compatibility on the original pairs, expressed in the marked
Picard coordinates, gives equality of their positively numbered toric periods. -/
theorem orderedBoundaryPeriod_eq_of_signed_boundaryPeriod
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (hU : IsNodalBoundaryTower E (Y ↘ S) (𝟙 Y) U)
    (hp : p ≫ (X ↘ S) = π c ≫ base) (hq : q ≫ (Y ↘ S) = π d ≫ base)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hE : (E.comap q).support = (ι d).ker.support)
    (G : LineBundleClass Y → LineBundleClass X)
    (hPic : ∀ L : LineBundleClass Y, (mark c).symm (Additive.ofMul (pullback p (G L))) =
      (mark d).symm (Additive.ofMul (pullback q L)))
    {f : Btor ⟶ D.subscheme} {g : Btor ⟶ E.subscheme}
    (hf : f ≫ D.subschemeι = ι c ≫ p) (hg : g ≫ E.subschemeι = ι d ≫ q)
    (hfs : f.IsOrientedCycleSubdivision C A) (act : DihedralGroup n)
    (hgs : g.IsOrientedCycleSubdivision C
      (if DihedralGroup.cycleOrientationSign act = -1 then B.reverse else B))
    (hCartierD : D.IsEffectiveCartier) (hCartierE : E.IsEffectiveCartier)
    (gD : ∀ v : irreducibleComponents (D.subscheme.singularLocus ℂ).blowup,
      (D.subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (gE : ∀ v : irreducibleComponents (E.subscheme.singularLocus ℂ).blowup,
      (E.subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (hOrth : ∀ x : E.boundaryOrthogonal ℂ,
      Additive.ofMul (G x.val.toMul) ∈ D.boundaryOrthogonal ℂ)
    (hperiod : ∀ x : E.boundaryOrthogonal ℂ,
      hCartierE.boundaryPeriod gE B.endpoint_eq (ofAdd x) =
        hCartierD.boundaryPeriod gD A.endpoint_eq (ofAdd ⟨_, hOrth x⟩) ^
          (DihedralGroup.cycleOrientationSign act : ℤ))
    : orderedBoundaryPeriod hΦ b s C (center c) =
      orderedBoundaryPeriod hΦ b s C (center d) := by
  obtain ⟨eD, heD, hDs, hfD, hmarkD⟩ :=
    exists_period_presentation b s hΦ c e hp (by simpa only [comap_comp] using hD) f hf
  obtain ⟨eE, heE, hEs, hgE, hmarkE⟩ :=
    exists_period_presentation b s hΦ d e' hq (by simpa only [comap_comp] using hE) g hg
  let B' := if DihedralGroup.cycleOrientationSign act = -1 then B.reverse else B
  have hsubD : (toricBoundaryToBase (J[c]) eD hDs).IsOrientedCycleSubdivision C A := hfD ▸ hfs
  have hsubE : (toricBoundaryToBase (J[d]) eE hEs).IsOrientedCycleSubdivision C B' :=
    hgE ▸ hgs
  rw [← markedBoundaryPeriod_eq_orderedBoundaryPeriod hΦ b s C hT eD heD hDs
      hCartierD gD A hsubD,
    ← markedBoundaryPeriod_eq_orderedBoundaryPeriod hΦ b s C hU eE heE hEs
      hCartierE gE B' hsubE]
  apply MonoidHom.ext
  intro x
  let xD := (markedBoundaryChargeEquiv hΦ b s hT eD heD hDs).symm x.toAdd
  let xE := (markedBoundaryChargeEquiv hΦ b s hU eE heE hEs).symm x.toAdd
  have hmap : G xE.val.toMul = xD.val.toMul := by
    dsimp only [xE, xD]
    rw [coe_markedBoundaryChargeEquiv_symm, coe_markedBoundaryChargeEquiv_symm]
    exact map_picardBoundaryOrthogonalEquivChargeKernel_symm_of_matching_markings
      hΦ b s hT hU eD eE heD heE hDs hEs G x.toAdd
      ((hmarkD _).trans ((hPic _).trans (hmarkE _).symm))
  have hx : (⟨_, hOrth xE⟩ : D.boundaryOrthogonal ℂ) = xD :=
    Subtype.ext (congrArg Additive.ofMul hmap)
  have h := hperiod xE
  rw [hx] at h
  have hpD := markedBoundaryPeriod_apply hΦ b s hT eD heD hDs hCartierD gD A x.toAdd
  have hpE := markedBoundaryPeriod_apply hΦ b s hU eE heE hEs hCartierE gE B' x.toAdd
  rw [ofAdd_toAdd] at hpD hpE
  rw [hpD, hpE]
  -- The target subdivision is numbered in the positive toric orientation.
  rcases Int.units_eq_one_or (DihedralGroup.cycleOrientationSign act) with hsign | hsign
  · have hne : (1 : ℤˣ) ≠ -1 := by decide
    simpa only [B', hsign, ite_eq_right hne, Units.val_one, zpow_one] using h.symm
  · have hr :
        hCartierE.boundaryPeriod gE B.reverse.endpoint_eq (ofAdd xE) =
          (hCartierE.boundaryPeriod gE B.endpoint_eq (ofAdd xE))⁻¹ := by
      rw [IsEffectiveCartier.boundaryPeriod_apply, IsEffectiveCartier.boundaryPeriod_apply]
      exact B.nodalPicardCycleMulEquiv_reverse
        (hCartierE.restrictBoundaryOrthogonal gE (ofAdd xE))
    simp only [hsign, Units.val_neg, Units.val_one, zpow_neg_one] at h
    simpa only [B', hsign, ite_true, inv_inv] using (hr.trans (congrArg Inv.inv h)).symm

/-- When two nodal pairs have common ordered toric Picard coordinates, a
surjective prescribed Picard map with the signed period equation is realized by
an isomorphism of pairs with the specified action on the ordered boundary
branches. The marked pullbacks determine which rays survive the contractions. -/
theorem exists_iso_of_signed_boundary_period_of_matching_picard_markings
    (hc : Φ.IsComplete) (u : ZMod m ≃ Φ.Ray)
    (hvertices : ∀ j, (Btor).dualGraphVertexEquiv aT (C.vertex j) =
      Φ.boundaryNormalizationComponentEquiv hΦ (u j))
    (hdet : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ ∧
      (Φ.boundaryIdeal h₀).subschemeι ((Btor).dualGraphEdgeEquiv aT (C.edge j)).val =
        Φ.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ))
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (hU : IsNodalBoundaryTower E (Y ↘ S) (𝟙 Y) U)
    (hp : p ≫ (X ↘ S) = π c ≫ base) (hq : q ≫ (Y ↘ S) = π d ≫ base)
    (hD : (D.comap p).support = (ι c).ker.support)
    (hE : (E.comap q).support = (ι d).ker.support)
    (G : LineBundleClass Y → LineBundleClass X) (hG : Function.Surjective G)
    (hPic : ∀ L : LineBundleClass Y, (mark c).symm (Additive.ofMul (pullback p (G L))) =
      (mark d).symm (Additive.ofMul (pullback q L)))
    {f : Btor ⟶ D.subscheme} {g : Btor ⟶ E.subscheme} [f.IsOver S] [g.IsOver S]
    (hf : f ≫ D.subschemeι = ι c ≫ p) (hg : g ≫ E.subschemeι = ι d ≫ q)
    (hfs : f.IsOrientedCycleSubdivision C A) (act : DihedralGroup n)
    (hgs : g.IsOrientedCycleSubdivision C
      (if DihedralGroup.cycleOrientationSign act = -1 then B.reverse else B))
    (hCartierD : D.IsEffectiveCartier) (hCartierE : E.IsEffectiveCartier)
    (gD : ∀ v : irreducibleComponents (D.subscheme.singularLocus ℂ).blowup,
      (D.subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (gE : ∀ v : irreducibleComponents (E.subscheme.singularLocus ℂ).blowup,
      (E.subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (hOrth : ∀ x : E.boundaryOrthogonal ℂ,
      Additive.ofMul (G x.val.toMul) ∈ D.boundaryOrthogonal ℂ)
    (hperiod : ∀ x : E.boundaryOrthogonal ℂ,
      hCartierE.boundaryPeriod gE B.endpoint_eq (ofAdd x) =
        hCartierD.boundaryPeriod gD A.endpoint_eq (ofAdd ⟨_, hOrth x⟩) ^
          (DihedralGroup.cycleOrientationSign act : ℤ))
    (ρ : Φ.Ray)
    (hρ : p (prime[c] ρ).val = D.subschemeι (A.componentGenericPoint 0))
    (hρ' : q (prime[d] ρ).val =
      E.subschemeι (B.componentGenericPoint (DihedralGroup.cycleVertexPerm act 0))) :
    ∃ (a : X ≅ Y) (aB : D.subscheme ≅ E.subscheme) (haB : aB.hom.IsOver S),
      a.hom ≫ (Y ↘ S) = (X ↘ S) ∧ E.comap a.hom = D ∧
      aB.hom ≫ E.subschemeι = D.subschemeι ≫ a.hom ∧
      (∀ L : LineBundleClass Y, pullback a.hom L = G L) ∧
      (letI := haB; aB.boundaryCycleAction A B = act) := by
  have hkeep := mem_boundaryPrimes_iff_of_matching_picard_markings hΦ b s
    (center c) hT e.symm hp hD (center d) hU e'.symm hq hE
    (LinearMap.IsPerfPair.separatingRight inferInstance) G hG hPic
  have htoric := orderedBoundaryPeriod_eq_of_signed_boundaryPeriod hΦ b s c d e e' A B C
    hT hU hp hq hD hE G hPic hf hg hfs act hgs
    hCartierD hCartierE gD gE hOrth hperiod
  exact exists_iso_of_eq_period_of_matching_picard_markings hΦ b s c d e e' A B C
    hc u hvertices hdet hnodes hT hU hp hq hD hE hkeep htoric G hPic
    hf hg hfs act hgs ρ hρ hρ'

end TauCeti.Toric.Fan
