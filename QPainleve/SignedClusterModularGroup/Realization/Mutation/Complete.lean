/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Subdivision
public import QPainleve.SignedClusterModularGroup.Realization.Mutation.Contracted
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Geometry.Toric.Fan.StarSubdivision.RayInsertion
import QPainleve.SignedClusterModularGroup.Realization.Refinement

/-!
# Mutation of marked presentations on complete fans

The elementary transformation of Gross, Hacking and Keel,
[*Birational geometry of cluster algebras*, §3.1](https://arxiv.org/html/1309.2573v2#S3.SS1),
uses a fan containing both pivot directions. A regular subdivision inserts the
opposite ray for the entire marked family. Mutation then gives a new complete
presentation on the same prescribed center domain, with its ordered nodal
contractions and marked Picard pullbacks.
-/

public section

open AlgebraicGeometry CategoryTheory PointedCone
open Module (Basis)
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

open GeometricRealization (CenterPoint Point)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {n : ℕ}
  {L : Type} [AddCommGroup L] {γ : Type*}
  (Q : CompleteToricPresentation k₀ i b (n + 1) L γ) (k : Fin (n + 1))

local notation "S" => Spec (CommRingCat.of k₀)
local notation "A" => (Fin (n + 1) → ℤ)
local notation "Centers" => Over.mk (structureMap k₀ A)
local notation "XTor" => scheme k₀ (Fin (n + 1) →₀ ℤ)
local notation "χ(" c ")" => pointsEquiv k₀ A
  (Subtype.mk (CommaMorphism.left (c : Point Centers)) (Over.w (c : Point Centers)))
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme
  (Fan.toricBoundaryIdeal k₀ Φ h)

variable {E : SkewExchangeMatrix (Fin (n + 1))} (P : ChargeSeed E N)
  (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = rayChargeMap Q.rays)

local notation "w" => Quiver.Hom.toPath (Generator.toStep (Generator.mutate k) E)
local notation "C" => Quiver.Path.centerPartialMap k₀ w P
local notation "F" => Quiver.Path.xRationalMap k₀ w

variable (U : (scheme k₀ (Fin (n + 1) → ℤ)).Opens)
  (hU : Dense (U : Set (scheme k₀ (Fin (n + 1) → ℤ))))
  (hle : U ≤ (Quiver.Path.centerPartialMap k₀ ((Generator.mutate k).toStep E).toPath P).domain)

local notation "C'" => Scheme.PartialMap.restrict C U hU hle
local notation "src(" c ")" => (c) ≫ Scheme.PartialMap.domainSource (X := Centers) (Y := Centers) C'
local notation "dst(" c ")" => (c) ≫ Scheme.PartialMap.domainTarget (X := Centers) (Y := Centers) C'

variable {m : ℕ} [NeZero m] {H : LinearMap.BilinForm ℤ L}
  (M : Point (Over.mk (structureMap k₀ (Fin (n + 1) → ℤ))) →
    MarkedSurface k₀ m H (scheme k₀ (Fin (n + 1) →₀ ℤ)))

include hform hcharge in
/-- A mutation of a complete marked toric presentation gives a target presentation and
a realization over the prescribed dense open of the mutation domain. The contracted
Picard marking and numbered branches are preserved, and the fiber isomorphism identifies
the target pair with the original pair carrying its new evaluation. A single regular
subdivision supplies the opposite pivot ray. The target rays and auxiliary Picard
inclusion come from mutation after lifting to that subdivision. -/
theorem exists_mutated_presentation
    (hmodel : ∀ c : CenterPoint (U := Centers) (V := Centers) C',
      Q.HasNodalModel (src(c)) (M (src(c)))) :
    ∃ (Q' : CompleteToricPresentation k₀ i b (n + 1) L Empty)
      (M' : Point Centers → MarkedSurface k₀ m H XTor)
      (R : GeometricRealization (T₀ := Centers) (T₁ := Centers) M M' C' F),
      (Quiver.Path.chargeTarget w P).charge = rayChargeMap Q'.rays ∧
      R.picard = .refl H ∧ R.boundaryAction = 1 ∧
      (∀ c : CenterPoint (U := Centers) (V := Centers) C',
        ∃ (ev : (M (src(c))).surface ⤏ XTor)
          (hM : M' (dst(c)) = (M (src(c))).withEvaluation ev),
          (R.fiber c).iso ≪≫ eqToIso (congrArg MarkedSurface.pair hM) = Iso.refl _ ∧
          Q'.HasNodalModel (dst(c)) (M' (dst(c)))) ∧
      ∃ (Ω : Fan i) (h : Ω.IsSubdivision Q.fan) (hΩ : Ω.IsRegular) (_ : Ω.IsComplete)
        (hopp : hull ℝ {i (-(h.liftRay (Q.rays k)).primitiveGenerator)} ∈ Ω.cones),
        let s₀ := h.liftRay ∘ Q.rays
        let hv := (s₀ k).primitiveGenerator_ne_zero
        let hp := (s₀ k).hull_primitiveGenerator_mem
        let Ψ := Ω.mutationFan b hv hp hopp
        ∃ hfan : Q'.fan = Ψ,
          (hfan ▸ Q'.rays : Fin (n + 1) → Ψ.Ray) = Ω.mutationFanCenterRays b s₀ k hopp ∧
          (hfan ▸ Q'.inclusion :
            L →ₗ[ℤ] Additive (LineBundleClass (Ψ.finiteFanScheme k₀)) × (Fin (n + 1) → ℤ)) =
            (mutationPicardEquiv k₀ b s₀ k hopp hΩ).symm.toLinearMap.comp
              ((h.internalBlowupPicardPullback k₀).comp Q.inclusion) := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  have hN := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  obtain ⟨Ω, h, hΩ, hcΩ, hopp⟩ :=
    (Q.rays k).exists_regular_subdivision_containing_opposite Q.regular Q.complete hN
  let : Nonempty Ω.cones := hcΩ.nonempty_cones
  let s₀ := h.liftRay ∘ Q.rays
  let hv := (s₀ k).primitiveGenerator_ne_zero
  let hp := (s₀ k).hull_primitiveGenerator_mem
  let Ψ := Ω.mutationFan b hv hp hopp
  let hcΨ : Ψ.IsComplete := (Ω.isComplete_mutationFan_iff b hv hp hopp).mpr hcΩ
  let : Nonempty Ψ.cones := hcΨ.nonempty_cones
  choose p Y d W e hW he using fun c ↦ (Q.hasNodalModel_iff _ _).mp (hmodel c)
  obtain ⟨hpre, l', hl', hnumbering⟩ :=
    ContractedToricFiber.exists_positive_subdivision_family (δ := Empty) h
      (fun c : CenterPoint (U := Centers) (V := Centers) C' ↦ χ(src(c)))
      (fun c ↦ M (src(c))) p hΩ Q.complete (fun c ↦ ⟨Y c, d c, W c, e c, hW c, he c⟩)
      Q.rayOrder Q.component_eq Q.positive
  let : PrestableFamily (Dtor[Ω,hcΩ.nonempty_cones] ↘ S) := hpre
  let : NeZero l' := hl'
  obtain ⟨T₀, o₀, v₀, hv₀, hpos₀, -, -, hmodels₀⟩ := hnumbering Empty.elim
  have hcharge₀ : P.charge = rayChargeMap s₀ := hcharge.trans (h.rayChargeMap_liftRay Q.rays).symm
  obtain ⟨hpre', T', M', R, hv', hpos', hcharge', hpic, hact, hmodels'⟩ :=
    GeometricRealization.exists_mutate_contracted b s₀ k hopp hΩ P hform hcharge₀ U hU hle M
      v₀ hcΩ hv₀ hpos₀ (T := T₀) (o := o₀)
      (J := (h.internalBlowupPicardPullback k₀).comp Q.inclusion) (fun c ↦ by
        obtain ⟨q, Y, d, W, e, hW, he, -⟩ := hmodels₀ c
        exact ⟨q, Y, d, W, e, hW, he⟩)
  let Q' : CompleteToricPresentation k₀ i b (n + 1) L Empty :=
    { fan := Ψ
      complete := hcΨ
      regular := (Ω.isRegular_mutationFan_iff b hv hp hopp).mpr hΩ
      rays := Ω.mutationFanCenterRays b s₀ k hopp
      prestable := hpre'
      length := l'
      neZero := hl'
      marks := Empty.elim
      cycle := T'
      origin := o₀
      inclusion := (mutationPicardEquiv k₀ b s₀ k hopp hΩ).symm.toLinearMap.comp
        ((h.internalBlowupPicardPullback k₀).comp Q.inclusion)
      rayOrder := v₀.trans (Ω.mutationFanRayEquiv b hv hp hopp)
      component_eq := hv'
      positive := hpos' }
  refine ⟨Q', M', R, hcharge', hpic, hact, ?_, Ω, h, hΩ, hcΩ, hopp, rfl, rfl, rfl⟩
  intro c
  obtain ⟨ev, hM, hIso, hp⟩ := hmodels' c
  exact ⟨ev, hM, hIso, (Q'.hasNodalModel_iff _ _).mpr hp⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
