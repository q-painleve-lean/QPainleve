/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Period.Surjectivity
public import QPainleve.SignedClusterModularGroup.Realization.MarkedComparison

import QPainleve.AlgebraicGeometry.Curves.Node.Period.Orientation

/-!
# Period transport in a marked toric presentation

The boundary period on a marked surface agrees with the toric period of its
charge class. A realized pair isomorphism therefore transports ordered boundary
periods by the marked Picard pullback and the sign on the ordered branches.

The gluing period and center variation are those of Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, §2.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData TopologicalSpace
open LineBundleClass

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" P "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair P)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n] {L : Type} [AddCommGroup L]
  {B : LinearMap.BilinForm ℤ L}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}

local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))
local notation "Dtor" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h₀)
local notation "center" c:arg => (fun j : Fin r ↦ c (ofAdd (Pi.single j 1)))
local notation "Model[" c "]" => Fan.internalBlowupTower b s (center c)
local notation "ChargeKernel" => LinearMap.ker (Fan.rayChargeMap s)
local notation "A" => Chow.intersectionBilinForm ℂ Φ.algebraicRealization
local notation "Qform" =>
  LinearMap.BilinForm.prod A (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))

variable [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ S)]
  {γ : Type*} {a : γ → ((Φ.boundaryIdeal h₀).subscheme ↘ S).smoothLocus}
  {T : NodalCycleNumbering a m} {origin : ZMod m}
  {ι : L →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  [Φ.algebraicRealization.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S)]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm ℂ Φ.algebraicRealization).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ))))]

local notation "aux" => (LinearEquiv.symm (Fan.boundaryOrthogonalEquivChargeKernel hΦ s Qform))
local notation "period[" c "]" => Fan.orderedBoundaryPeriod hΦ b s T (center c)
local notation "normKer[" C "]" =>
  MonoidHom.ker (pullbackHom (blowupToBase (Scheme.singularLocus ℂ C)))

variable {c d : Multiplicative (Fin r → ℤ) →* ℂˣ} {P Q : MarkedSurface ℂ n B Xtor[r]}
  (p : ContractedToricFiber (h₀ := h₀) b s hΦ T origin ι c P)
  (q : ContractedToricFiber (h₀ := h₀) b s hΦ T origin ι d Q)

local instance (M : MarkedSurface ℂ n B Xtor[r]) : PrestableFamily (D[M].subscheme ↘ S) :=
  M.prestable_boundaryImage

local instance (M : MarkedSurface ℂ n B Xtor[r]) :
    SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth

local instance (M : MarkedSurface ℂ n B Xtor[r]) : M.surface.IsProjectiveOver ℂ :=
  M.projective

namespace ContractedToricFiber

include p in
/-- The period of a marked class on the contracted surface is the ordered toric
period of its charge vector, with the orientation induced by the subdivision. -/
theorem orderedBoundaryPeriod_eq_boundaryPeriod (hD : D[P].IsEffectiveCartier)
    (hgenus : ∀ v : irreducibleComponents (D[P].subscheme.singularLocus ℂ).blowup,
      (D[P].subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (z : L) (hz : P.picardMarking z ∈ D[P].boundaryOrthogonal ℂ)
    (x : ChargeKernel) (hx : ι z = (aux x).val) :
    period[c] (ofAdd x) =
      hD.boundaryPeriod hgenus P.imageCycle.endpoint_eq (ofAdd ⟨P.picardMarking z, hz⟩) := by
  let f := p.boundaryMap ≫ P.boundaryImageIso.hom
  let u := hD.restrictBoundaryOrthogonal hgenus (ofAdd ⟨P.picardMarking z, hz⟩)
  obtain ⟨hu, hperiod⟩ := p.isOrientedCycleSubdivision_comp_boundaryImage.period_pullback u
  have hclass : (Fan.orderedBoundaryRestriction hΦ b s (center c) (ofAdd x) : normKer[Dtor]) =
      ⟨pullback f u.val, hu⟩ := by
    apply Subtype.ext
    have hmark := congrArg (Fan.internalBlowupPicardMarking b s (center c) hΦ)
      ((p.marked_pullback z).trans hx)
    simp only [LinearEquiv.apply_symm_apply] at hmark
    have hf : f ≫ D[P].subschemeι = (Model[c]).2.boundaryι ≫ p.projection := by
      simpa only [f, Category.assoc, MarkedSurface.boundaryImageIso_hom_comp]
        using p.boundary_comp
    rw [Fan.coe_orderedBoundaryRestriction_eq_pullback_internalBlowupPicardMarking,
      ← hmark, toMul_ofMul]
    simp only [u, IsEffectiveCartier.restrictBoundaryOrthogonal_apply, toAdd_ofAdd]
    rw [pullback_comp f, hf, pullback_comp]
  rw [Fan.orderedBoundaryPeriod_apply, hclass, hperiod, IsEffectiveCartier.boundaryPeriod_apply]

include p q in
/-- An isomorphism of marked fibers transports the toric period of a target charge
class by its marked Picard pullback and its action on the actual boundary branches. -/
theorem orderedBoundaryPeriod_apply_of_pullback
    (hp : D[P].IsEffectiveCartier) (hq : D[Q].IsEffectiveCartier)
    (gp : ∀ v : irreducibleComponents (D[P].subscheme.singularLocus ℂ).blowup,
      (D[P].subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    (gq : ∀ v : irreducibleComponents (D[Q].subscheme.singularLocus ℂ).blowup,
      (D[Q].subscheme.blowupComponent (K := ℂ) v).toScheme.genus ℂ = 0)
    {F : Xtor[r] ⤏ Xtor[r]} {I : B.IsometryEquiv B} {g : DihedralGroup n}
    (R : FiberRealization P Q F I g)
    (z : L) (hz : Q.picardMarking z ∈ D[Q].boundaryOrthogonal ℂ)
    (x y : ChargeKernel) (hx : ι z = (aux x).val) (hy : ι (I z) = (aux y).val) :
    period[c] (ofAdd y) = (period[d] (ofAdd x)) ^ (cycleOrientationSign g : ℤ) := by
  let e := MarkedSurface.imagePairIso R.iso
  let η := cycleOrientationSign g
  let swap := decide (η = -1)
  have hg : e.boundaryCycleAction P.imageCycle Q.imageCycle = g :=
    (MarkedSurface.imagePairIso_boundaryAction R.iso).trans R.boundaryAction_eq
  have horder := e.branchOrder_boundaryCycleAction P.imageCycle Q.imageCycle
  rw [hg] at horder
  obtain ⟨hs, hperiod⟩ := hp.boundaryPeriod_pullback gp P.imageCycle.endpoint_eq
    hq gq Q.imageCycle.endpoint_eq (MarkedSurface.surfaceIso R.iso).hom e
    (MarkedSurface.imagePairIso_hom_comp R.iso).symm swap
    (by simpa only [swap, η, decide_eq_true_eq] using horder) (ofAdd ⟨Q.picardMarking z, hz⟩)
  simp only [toAdd_ofAdd, Subtype.coe_mk] at hs hperiod
  have hs' : P.picardMarking (I z) ∈ D[P].boundaryOrthogonal ℂ := R.picard_eq z ▸ hs
  have hclass :
      (⟨Additive.ofMul
        (pullback (MarkedSurface.surfaceIso R.iso).hom (Q.picardMarking z).toMul), hs⟩ :
          D[P].boundaryOrthogonal ℂ) = ⟨P.picardMarking (I z), hs'⟩ :=
    Subtype.ext (R.picard_eq z).symm
  rw [hclass] at hperiod
  rw [p.orderedBoundaryPeriod_eq_boundaryPeriod hp gp (I z) hs' y hy,
    q.orderedBoundaryPeriod_eq_boundaryPeriod hq gq z hz x hx]
  rcases Int.units_eq_one_or η with h | h
  · have hne : (1 : ℤˣ) ≠ -1 := by decide
    simpa only [swap, h, hne, decide_false, Bool.false_eq_true, ite_false, Units.val_one,
      η, zpow_one] using hperiod
  · simpa only [swap, h, decide_true, ite_true, Units.val_neg, Units.val_one, η, zpow_neg_one]
      using hperiod

end ContractedToricFiber

end QPainleve.SignedClusterModularGroup
