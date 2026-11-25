/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Period.Noncollision
public import QPainleve.SignedClusterModularGroup.Boundary.Restriction
public import QPainleve.SignedClusterModularGroup.Realization.Orthogonal
public import QPainleve.SignedClusterModularGroup.Realization.Period

import QPainleve.AlgebraicGeometry.Curves.Node.Period.Roots
import QPainleve.Geometry.Toric.Fan.Presentation.Genus
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Boundary
import TauCeti.AlgebraicGeometry.RationalPoint.Image

/-!
# Root-free fibers with compatible periods

A signed boundary isometry prescribes a relation between the periods of two fibers
of a fixed marked toric presentation. The centers can be chosen before a word is
known, in every word's noncollision domain. The geometric periods then satisfy
the signed pullback equation on the actual Picard groups, and neither fiber has a
prime curve disjoint from its boundary.

This uses the toric center description of periods from Gross, Hacking and Keel,
[Proposition 2.9](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

open SignedBoundaryIsometryGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "Xtor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "center[" c "]" => (fun j ↦ c (ofAdd (Pi.single j 1)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}

local instance periodFiberPrestable (M : MarkedSurface ℂ n B Xtor[r]) :
    PrestableFamily (D[M].subscheme ↘ S) :=
  M.prestable_boundaryImage

local instance periodFiberSmooth (M : MarkedSurface ℂ n B Xtor[r]) :
    SmoothOfRelativeDimension 2 (M.surface ↘ S) :=
  M.smooth

local instance periodFiberProjective (M : MarkedSurface ℂ n B Xtor[r]) :
    M.surface.IsProjectiveOver ℂ :=
  M.projective

namespace CompleteToricPresentation

open Fan

variable (Q : CompleteToricPresentation i b r L γ)
  {M : GeometricRealization.Point Centers[r] → MarkedSurface ℂ n B Xtor[r]}

local instance periodFanNonempty : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance periodCycleNeZero : NeZero Q.length := Q.neZero
local instance periodFanPrestable :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "ChargeKernel" => LinearMap.ker (rayChargeMap Q.rays)

local notation "Aux" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Q.fan.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin r → ℤ)))
local notation "period[" c "]" => orderedBoundaryPeriod Q.regular b Q.rays Q.cycle center[χ[c]]

private theorem exists_compatible_ordered_periods
    {E : SkewExchangeMatrix (Fin r)} (P : ChargeSeed E N) (hcharge : P.charge.ker ≤ ChargeKernel)
    [Q.fan.algebraicRealization.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (Q.fan.algebraicRealization ↘ S)] [(Aux).IsPerfPair]
    (f : ChargeKernel ≃ₗ[ℤ] ChargeKernel) :
    ∃ c₀ c₁ : GeometricRealization.Point Centers[r],
      Function.Injective period[c₀] ∧ Function.Injective period[c₁] ∧
      (∀ x : ChargeKernel, period[c₁] (ofAdd x) = period[c₀] (ofAdd (f x))) ∧
      ∀ ⦃C : SkewExchangeMatrix (Fin r)⦄ (w : Word E C),
        c₀.left (default : S) ∈ w.centerOpen ℂ P ∧ c₁.left (default : S) ∈ w.centerOpen ℂ P := by
  obtain ⟨t₀, t₁, hi₀, hi₁, hper, hword⟩ :=
    exists_ordered_boundary_periods_mem_all_center_opens Q.regular b Q.rays Q.cycle Q.rayOrder
      (fun j ↦ (Q.cycle.component_apply j).symm.trans (Q.component_eq j))
      (fun j ↦ (Q.positive j).1)
      Q.exists_cone_of_numbered_node P hcharge f 1
  refine ⟨centerPoint t₀, centerPoint t₁, ?_, ?_, ?_, fun _ w ↦ hword w⟩
  · simpa only [centerPoint_parameters] using hi₀
  · simpa only [centerPoint_parameters] using hi₁
  · intro x
    simpa only [centerPoint_parameters, Units.val_one, zpow_one] using hper x

/-- A prescribed signed boundary isometry has compatible geometric periods at
two root-free fibers of the same presentation. Both centers belong to every
finite word's noncollision domain. The geometric periods use the genus-zero
normalized components of the selected fibers. The surface models are required
only on the noncollision open of the empty word. -/
theorem exists_root_free_fibers_with_compatible_periods
    {E : SkewExchangeMatrix (Fin r)} (P : ChargeSeed E N) (hcharge : P.charge.ker ≤ ChargeKernel)
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    {d : ZMod n → L} (hmark : ∀ c, (M c).boundaryClass (hD c) = d)
    (g : signedBoundaryIsometryGroup B d)
    (hmodels : ∀ c : GeometricRealization.Point Centers[r],
      c.left (default : S) ∈ (Path.nil : Word E E).centerOpen ℂ P → Q.HasNodalModel c (M c)) :
    ∃ c₀ c₁ : GeometricRealization.Point Centers[r],
      Q.HasNodalModel c₀ (M c₀) ∧ Q.HasNodalModel c₁ (M c₁) ∧
      (∀ ⦃C : SkewExchangeMatrix (Fin r)⦄ (w : Word E C),
        c₀.left (default : S) ∈ w.centerOpen ℂ P ∧ c₁.left (default : S) ∈ w.centerOpen ℂ P) ∧
      (∀ z : CodimensionOnePoint (M c₀).surface, ¬Disjoint (closure {(z : (M c₀).surface)})
        (D[M c₀].support : Set (M c₀).surface)) ∧
      (∀ z : CodimensionOnePoint (M c₁).surface, ¬Disjoint (closure {(z : (M c₁).surface)})
        (D[M c₁].support : Set (M c₁).surface)) ∧
      ∃ (hg₀ : ∀ v : irreducibleComponents (D[M c₀].subscheme.singularLocus ℂ).blowup,
          (D[M c₀].subscheme.blowupComponent v).toScheme.genus ℂ = 0)
        (hg₁ : ∀ v : irreducibleComponents (D[M c₁].subscheme.singularLocus ℂ).blowup,
          (D[M c₁].subscheme.blowupComponent v).toScheme.genus ℂ = 0),
        ∀ x : D[M c₁].boundaryOrthogonal ℂ,
          let y := (M c₀).picardMarking
            ((toIsometry B d g).val ((M c₁).picardMarking.symm x.val))
          ∃ hy : y ∈ D[M c₀].boundaryOrthogonal ℂ,
            (hD c₁).boundaryPeriod hg₁ (M c₁).imageCycle.endpoint_eq (ofAdd x) =
              ((hD c₀).boundaryPeriod hg₀ (M c₀).imageCycle.endpoint_eq
                (ofAdd ⟨y, hy⟩)) ^ (sign B d g : ℤ) := by
  classical
  let : Q.fan.algebraicRealization.IsProjectiveOver ℂ :=
    Q.fan.isProjectiveOver_algebraicRealization_of_isComplete Q.regular Q.complete b
  let := Q.smoothOfRelativeDimension_fan
  let U := (Path.nil : Word E E).centerOpen ℂ P
  obtain ⟨z, hz, hzU⟩ := U.isOpen.isLocallyClosed.exists_rationalPoint_mem
    (structureMap ℂ (Fin r → ℤ)) ((Path.nil : Word E E).nonempty_centerOpen (K := ℂ) P)
  let c : GeometricRealization.Point Centers[r] := Over.homMk z hz
  have hc : c.left (default : S) ∈ U := by
    rw [Subsingleton.elim (default : S) (IsLocalRing.closedPoint ℂ)]
    exact hzU
  let := Q.isPerfPair_auxiliaryPicardForm
  let e := (hmodels c hc).chargeKernelEquiv (hD c) (hmark c)
  have he := (hmodels c hc).chargeKernelEquiv_symm_apply (hD c) (hmark c)
  -- The charge action already incorporates the boundary sign.
  let action := (e.symm.trans (signedOrthogonalRestriction B d g).val).trans e
  obtain ⟨c₀, c₁, hi₀, hi₁, hperiod, hword⟩ := Q.exists_compatible_ordered_periods P hcharge action
  have hm₀ := hmodels c₀ (hword Path.nil).1
  have hm₁ := hmodels c₁ (hword Path.nil).2
  obtain ⟨p₀, _⟩ := (Q.hasNodalModel_iff c₀ (M c₀)).mp hm₀
  obtain ⟨p₁, _⟩ := (Q.hasNodalModel_iff c₁ (M c₁)).mp hm₁
  let : IsIntegral (M c₀).surface := (M c₀).integral
  let : IsIntegral (M c₁).surface := (M c₁).integral
  have hg₀ := hm₀.hasToricPresentation.genus_blowupComponent_eq_zero (hD c₀)
  have hg₁ := hm₁.hasToricPresentation.genus_blowupComponent_eq_zero (hD c₁)
  refine ⟨c₀, c₁, hm₀, hm₁, fun _ w ↦ hword w, ?_, ?_, hg₀, hg₁, ?_⟩
  · exact (hD c₀).not_disjoint_primeDivisor_of_boundaryPeriod_injective
      hg₀ (M c₀).imageCycle.endpoint_eq
      ((p₀.orderedBoundaryPeriod_injective_iff (hD c₀) hg₀ (hmark c₀) e he).mp hi₀)
  · exact (hD c₁).not_disjoint_primeDivisor_of_boundaryPeriod_injective
      hg₁ (M c₁).imageCycle.endpoint_eq
      ((p₁.orderedBoundaryPeriod_injective_iff (hD c₁) hg₁ (hmark c₁) e he).mp hi₁)
  · exact p₀.boundaryPeriod_eq_of_orderedBoundaryPeriod_eq p₁ (hD c₀) (hD c₁)
      hg₀ hg₁ (hmark c₀) (hmark c₁) e he g (fun x ↦ hperiod x)

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
