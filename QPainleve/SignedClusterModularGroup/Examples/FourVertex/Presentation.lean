/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.InternalBlowup
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Internal

import QPainleve.Geometry.Toric.Fan.Boundary.DualGraph
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable

/-!
# Marked toric presentation of the four-vertex seed

The octagon with four ordered internal centers gives a complete marked
presentation of the doubled-square seed. The boundary numbering starts at
the ray `(1, 0)` and follows the positive cyclic order. The same Picard
coordinates and boundary classes apply throughout the center space.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory LinearMap Module
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedClusterModularGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.FourVertex

local notation "N" => (Fin 2 → ℤ)
local notation "i₂" => AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)
local notation "b₂" => Pi.basisFun ℤ (Fin 2)
local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers" => Over.mk (structureMap ℂ (Fin 4 → ℤ))
local notation "XTor" => scheme ℂ (Fin 4 →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

variable {Φ : Fan i₂} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)

local notation "Aux" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm ℂ Φ.algebraicRealization)
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin 4 → ℤ)))

/-- The positively numbered octagon gives a complete marked presentation with the
doubled-square exchange matrix. Any integral isometry to its ordered Picard
coordinates gives a marking. With this marking, the strict transform of each
numbered ray gives the same boundary class at every choice of the four centers.
The presentations retain the exceptional coefficients and the numbered rays
of the internal blowups. The numbered nodes and orders use the labels of
the integer tables for the generator words. -/
theorem exists_four_vertex_marked_presentation
    (v : ZMod 8 ≃ Φ.Ray) (hv : ∀ j, (v j).primitiveGenerator = octagonGenerator j)
    (hnext : ∀ j, (b₂).detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    letI : Φ.algebraicRealization.IsProjectiveOver ℂ :=
      Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b₂
    letI : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) := by
      rw [Fan.algebraicRealization_over]
      simpa only [finrank_pi, Fintype.card_fin] using
        Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
    ∀ {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L}
      (e : H.IsometryEquiv (Aux)),
    ∃ (Q : CompleteToricPresentation i₂ b₂ 4 L Empty)
      (P : ChargeSeed exchangeMatrix N)
      (M : GeometricRealization.Point Centers → MarkedSurface ℂ 8 H XTor)
      (hD : ∀ c, D[M c].IsEffectiveCartier),
      Q.length = 8 ∧ Q.origin = 0 ∧
      (∀ j : ZMod Q.length, (Q.rayOrder j).primitiveGenerator = octagonGenerator (j.val : ZMod 8)) ∧
      (∃ hfan : Q.fan = Φ, hfan ▸ Q.rays = diagonalRay v) ∧
      (∀ x, (Q.inclusion x).2 = (e x).2) ∧
      P.form = (b₂).detDualEquiv.toLinearMap ∧ P.charge = Fan.rayChargeMap Q.rays ∧
      (Fan.rayChargeMap Q.rays).range.toAddSubgroup.index = 2 ∧
      (∀ j : Fin 8, Fan.rayBoundaryOrders b₂ Q.rays (Q.rayOrder (j.val : ZMod Q.length)) =
        boundaryOrders j) ∧
      (letI := Q.prestable
       letI := Q.neZero
       ∀ j, ∃ σ : Q.fan.cones, (Q.rayOrder j).toCone ≤ σ ∧ (Q.rayOrder (j + 1)).toCone ≤ σ ∧
         (Q.fan.boundaryIdeal Q.complete.nonempty_cones).subschemeι
           ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme.dualGraphEdgeEquiv
             Q.marks (Q.cycle.edge j)).val =
           Q.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ)) ∧
      (letI := Q.complete.nonempty_cones
       letI := Q.prestable
       letI := Q.neZero
       ∀ c, Q.HasNodalModel c (M c) ∧
         (∃ p : ContractedToricFiber b₂ Q.rays Q.regular Q.cycle Q.origin Q.inclusion
           (pointsEquiv ℂ _ ⟨Over.Hom.left c, Over.w c⟩) (M c),
           p.IsNodalContraction ∧ ∀ j : Fin 8,
             p.numberedBoundaryRays (hD c) (ZMod.finEquiv 8 j) =
               Q.rayOrder (j.val : ZMod Q.length)) ∧
         ∀ j : ZMod 8, (M c).boundaryClass (hD c) j =
           e.symm (Φ.markedBoundaryMap hΦ (diagonalRay v) (Pi.single (v j) 1))) := by
  intro L _ H e
  classical
  have hN : Module.finrank ℤ N = 2 := by simp
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Φ.algebraicRealization.IsProjectiveOver ℂ :=
    Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b₂
  let : IsProper Φ.algebraicRealizationStructureMap := by
    rw [← Fan.algebraicRealization_over]
    infer_instance
  let D := Φ.boundaryIdeal hc.nonempty_cones
  let : PrestableFamily (D.subscheme ↘ S) := Φ.prestableFamily_boundary hΦ hc hN
  let marks : Empty → (D.subscheme ↘ S).smoothLocus := Empty.elim
  obtain ⟨edges, order, vertices, hend, hcomponent, hnodes⟩ :=
    Φ.exists_toric_boundary_dualGraph_cycle hΦ hc marks b₂ v hnext
  let C : Scheme.NodalCycleNumbering marks 8 := ⟨vertices, edges, order, hend⟩
  let Q : CompleteToricPresentation i₂ b₂ 4 L Empty :=
    { fan := Φ
      complete := hc
      regular := hΦ
      rays := diagonalRay v
      length := 8
      marks := marks
      cycle := C
      origin := 0
      inclusion := e.toLinearEquiv.toLinearMap
      rayOrder := v
      component_eq := fun j ↦ (C.component_apply j).trans (hcomponent j)
      positive := hnext }
  let P : ChargeSeed exchangeMatrix N :=
    { form := (b₂).detDualEquiv.toLinearMap
      charge := Fan.rayChargeMap (diagonalRay v)
      isAlt := (b₂).detDualEquiv_self
      matrix_eq := chargeExchangeMatrix_diagonalRay v hv }
  choose M p hmodel _ hnodal hD hclass using fun c : GeometricRealization.Point Centers ↦
    Q.exists_nodal_model_of_internalBlowup c e rfl
  have hcast : ∀ j : Fin 8, (j.val : ZMod 8) = ZMod.finEquiv 8 j := by decide
  refine ⟨Q, P, M, hD, rfl, rfl, ?_, ⟨rfl, rfl⟩, fun _ ↦ rfl, rfl, rfl,
    chargeIndex_diagonalRay v hv, ?_, ?_, ?_⟩
  · intro j
    exact (hv j).trans (congrArg octagonGenerator (ZMod.natCast_zmod_val j).symm)
  · intro j
    funext k
    have hj : octagonGenerator (j.val : ZMod 8) = boundaryRay j := by
      rw [octagonGenerator_apply, boundaryRay_eq, hcast, RingEquiv.symm_apply_apply]
    simp only [Q, Fan.rayBoundaryOrders_apply_eq_repr, Pi.basisFun_repr,
      primitiveGenerator_diagonalRay v hv, hv, hj, boundaryOrders_apply, Matrix.det_fin_two_of]
  · intro j
    obtain ⟨σ, h₀, h₁, he⟩ := hnodes j
    exact ⟨σ.val, h₀, h₁, he⟩
  · intro c
    refine ⟨hmodel c, ⟨p c, hnodal c, fun j ↦ ?_⟩, fun j ↦ ?_⟩
    · simpa only [Q, add_zero, hcast] using (hclass c (ZMod.finEquiv 8 j)).1
    · simpa only [Q, add_zero] using (hclass c j).2

end QPainleve.FourVertex
