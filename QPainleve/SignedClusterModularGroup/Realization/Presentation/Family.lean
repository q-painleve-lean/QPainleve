/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Boundary
public import QPainleve.SignedClusterModularGroup.Realization.Presentation

import QPainleve.Geometry.Toric.Fan.Picard.Contraction.MovingCenters.Tower
import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.MovingCenters
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Boundary

/-!
# Marked fibers over the toric center parameter space

A single marked nodal model of a complete toric presentation supplies models
at every choice of the centers, with the same Picard classes at the numbered
boundary components. The family is pointwise and permits repeated centers.
The construction combines `Fan.exists_nodal_contraction_of_same_surviving_rays`
with `CompleteToricPresentation.exists_nodal_model_of_same_contracted_rays`.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.BlowupTower QPainleve.CharacterTorus
open TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv k₀ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "centers[" c "]" => (fun j ↦ χ[c] (ofAdd (Pi.single j 1)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
  (Q : CompleteToricPresentation k₀ i b r L γ)
  {c : Point (Over.mk (QPainleve.CharacterTorus.structureMap k₀ (Fin r →
    ℤ)))} {M : MarkedSurface k₀ n H (QPainleve.CharacterTorus.scheme k₀ (Fin r →₀ ℤ))}

local instance : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance : NeZero Q.length := Q.neZero
local instance : PrestableFamily ((Q.fan.toricBoundaryIdeal k₀
  Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

variable [NeZero (2 : k₀)] in
private theorem exists_nodal_model_at_center
    (h : Q.HasNodalModel c M) (hD : D[M].IsEffectiveCartier) (d : Point Centers[r]) :
    ∃ (P : MarkedSurface k₀ n H XTor[r]), D[P].IsEffectiveCartier ∧ Q.HasNodalModel d P := by
  let : IsIntegral M.surface := M.integral
  let : M.surface.IsProjectiveOver k₀ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : Scheme.IsRationalOver (M.surface ↘ S) := h.isRationalOver
  let : PrestableFamily (D[M].subscheme ↘ S) := M.prestable_boundaryImage
  obtain ⟨p, _, _, T, a, hT, hp⟩ := (Q.hasNodalModel_iff c M).mp h
  have hn : AtWorstNodalOfRelativeDimensionOne (D[M].subschemeι ≫ M.surface ↘ S) := by
    rw [← over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hover :
      a.symm.hom ≫ T.toBase ≫ M.surface ↘ S =
        (Fan.internalBlowupTower k₀ b Q.rays centers[c]).2.toTower.toBase ≫
          (Q.fan.finiteFanSchemeToSpec k₀) := by
    rw [← Category.assoc, Iso.symm_hom, ← hp]
    exact p.projection_over
  obtain ⟨X, Y, t, D', U, e, hX, hproj, hsmooth, hCart, -, hprestable, -, hU, hbase, hred, hrays⟩ :=
    Q.fan.exists_nodal_contraction_of_same_surviving_rays k₀ b Q.rays Q.regular Q.complete
      centers[c] centers[d] hD hn (h.canonicalClass hD) hT a.symm hover (hp ▸ p.support_comap)
  let : X.Over S := ⟨t⟩
  let : IsIntegral X := hX
  let : X.IsProjectiveOver k₀ := hproj
  let : SmoothOfRelativeDimension 2 (X ↘ S) := hsmooth
  let : PrestableFamily (D'.subscheme ↘ S) := hprestable
  have hsupport := congrArg Scheme.IdealSheafData.support hred
  rw [support_radical] at hsupport
  obtain ⟨P, _, hP, hm, -⟩ :=
    Q.exists_nodal_model_of_same_contracted_rays hU e hbase hsupport p hT a hp hCart hD
      (fun ρ ↦ by simpa only [Iso.symm_hom, ← hp] using (hrays ρ).symm)
  exact ⟨P, hP, hm⟩

variable [NeZero (2 : k₀)] in
/-- Extend a marked nodal model to every choice of the ordered internal centers,
keeping the given model at the reference center. The Cartier boundary components
have constant classes in the common Picard lattice. -/
theorem exists_marked_family_of_nodal_model
    (h : Q.HasNodalModel c M) (hD : D[M].IsEffectiveCartier) :
    ∃ (P : Point Centers[r] → MarkedSurface k₀ n H XTor[r])
      (hP : ∀ d, D[P d].IsEffectiveCartier),
      P c = M ∧ ∀ d, Q.HasNodalModel d (P d) ∧ (P d).boundaryClass (hP d) = M.boundaryClass hD := by
  classical
  have hex (d : Point Centers[r]) :
      ∃ P : MarkedSurface k₀ n H XTor[r],
        D[P].IsEffectiveCartier ∧ Q.HasNodalModel d P ∧ (d = c → P = M) := by
    by_cases hd : d = c
    · subst d
      exact ⟨M, hD, h, fun _ ↦ rfl⟩
    · obtain ⟨P, hP, hm⟩ := Q.exists_nodal_model_at_center h hD d
      exact ⟨P, hP, hm, fun hh ↦ (hd hh).elim⟩
  choose P hP hm href using hex
  exact ⟨P, hP, href c rfl,
    fun d ↦ ⟨hm d, Q.boundaryClass_eq_of_matching_nodal_models (hm d) h (hP d) hD⟩⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
