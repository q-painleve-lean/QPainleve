/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
public import QPainleve.Geometry.Toric.Fan.Picard.Period.Noncollision
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Cremona.NodalModel
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.NodalPicardGroupIdentification

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group
import QPainleve.SignedClusterModularGroup.Realization.Surjectivity.Periods

/-!
# Cremona comparison on a root-free fiber

A reference surface of a marked toric presentation can have internal roots.
In the same marked family, period avoidance supplies a fiber without internal
roots whose center belongs to every word's noncollision open. The Cremona
projection on this fiber uses the family's signed Picard identification. Its
values are Picard pullback in the marking of the selected fiber, and its sign is
the inversion parity of a loop.

The center selection uses the compatible-period theorem with the identity
boundary isometry.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "δ[" M "]" =>
  (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf
    (MarkedSurface.isEffectiveCartier_boundaryIdeal M)))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {Q : CompleteToricPresentation i b r L γ} {E : SkewExchangeMatrix (Fin r)}

/-- In a marked toric family with one primitive nef square-zero reference fiber,
there is a fiber without any prime curve disjoint from its boundary. Its center
lies in the noncollision open of every word starting at the seed. The same
signed Picard identification gives the Cremona projection on that fiber and
computes its branch sign. -/
theorem NodalPicardGroupIdentification.exists_root_free_cremonaComparison
    {k : Type*} [Field k] {d : ZMod n → L}
    (G : NodalPicardGroupIdentification (B := B) Q k E d) {c : Point Centers[r]}
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ[G.family c]))
    (hnef : δ[G.family c].IsNef ℂ ((G.family c).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (G.family c).surface δ[G.family c] δ[G.family c] = 0) :
    ∃ a : Point Centers[r],
      let M := G.family a
      letI : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
      letI : M.surface.IsProjectiveOver ℂ := M.projective
      (∀ ⦃F : SkewExchangeMatrix (Fin r)⦄ (w : Word E F),
        a.left (default : S) ∈ w.centerOpen ℂ (Fan.rayChargeSeed b Q.rays hE)) ∧
      (∀ p : CodimensionOnePoint M.surface,
        ¬Disjoint (closure {(p : M.surface)}) (M.pair.hom.left.ker.support : Set M.surface)) ∧
      IsPrimitive (Additive.ofMul δ[M]) ∧ δ[M].IsNef ℂ (M.surface ↘ S) ∧
      Chow.classIntersectionNumber ℂ M.surface δ[M] δ[M] = 0 ∧
      ∃ P : ClusterCremonaComparison (k := k) E n (Chow.cremonaIsometryGroup ℂ M.surface),
        ∀ x : (SignedClusterModularGroup k E)ᵐᵒᵖ,
          (P.projection x).val = M.marking.isometryGroupCongr (toIsometry B d (G.signedEquiv x)) ∧
          P.sign x = (G.signedEquiv x).val.2 := by
  let hD (a : Point Centers[r]) := (G.family a).isEffectiveCartier_boundaryIdeal
  have hmark (z : Point Centers[r]) : (G.family z).boundaryClass (hD z) = d :=
    funext (G.boundaryClass_eq z)
  let P := Fan.rayChargeSeed b Q.rays hE
  have hcharge : P.charge.ker ≤ (Fan.rayChargeMap Q.rays).ker := by
    rw [Fan.rayChargeSeed_charge]
  obtain ⟨a, _, ha, _, hopen, hroot, _, _⟩ :=
    Q.exists_root_free_fibers_with_compatible_periods P hcharge hD hmark
      (1 : signedBoundaryIsometryGroup B d) (fun z _ ↦ G.hasNodalModel z)
  let M := G.family a
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : IsRationalOver (M.surface ↘ S) := ha.isRationalOver
  obtain ⟨hprim', hnef', hsq'⟩ :=
    ((G.family c).primitive_nef_square_zero_iff_of_boundaryClass_eq M (hD c) (hD a)
      (congrFun ((hmark c).trans (hmark a).symm))).mp
      ⟨hprim, hnef, hsq⟩
  let C := M.clusterCremonaComparison (congrArg Inv.inv (ha.canonicalClass (hD a)))
    hnef' hsq' (fun p hp ↦ (hroot p hp).elim) (hmark a)
    G.signedEquiv G.sign_ker_unop
  refine ⟨a, fun _ w ↦ (hopen w).1, hroot, hprim', hnef', hsq', C, fun x ↦ ⟨?_, ?_⟩⟩
  · simp only [C, M, MarkedSurface.val_clusterCremonaComparison_projection_apply]
  · simp only [C, MarkedSurface.clusterCremonaComparison_sign_apply]

/-- One primitive nef square-zero nodal model yields a Cremona comparison on a
root-free fiber of its marked toric family, while retaining the given reference
model. The projection and sign use the family's geometric Picard identification. -/
theorem exists_cluster_cremona_comparison_of_root_free_fiber
    {c : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}
    (href : Q.HasNodalModel c M₀)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul δ[M₀]))
    (hnef : δ[M₀].IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface δ[M₀] δ[M₀] = 0) :
    ∃ G : NodalPicardGroupIdentification (B := B) Q ℂ E
        (M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal),
      G.family c = M₀ ∧
      ∃ a : Point Centers[r],
        let M := G.family a
        letI : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
        letI : M.surface.IsProjectiveOver ℂ := M.projective
        (∀ ⦃F : SkewExchangeMatrix (Fin r)⦄ (w : Word E F),
          a.left (default : S) ∈ w.centerOpen ℂ (Fan.rayChargeSeed b Q.rays hE)) ∧
        (∀ p : CodimensionOnePoint M.surface,
          ¬Disjoint (closure {(p : M.surface)}) (M.pair.hom.left.ker.support : Set M.surface)) ∧
        IsPrimitive (Additive.ofMul δ[M]) ∧ δ[M].IsNef ℂ (M.surface ↘ S) ∧
        Chow.classIntersectionNumber ℂ M.surface δ[M] δ[M] = 0 ∧
        ∃ P : ClusterCremonaComparison (k := ℂ) E n (Chow.cremonaIsometryGroup ℂ M.surface),
          ∀ x : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ,
            (P.projection x).val = M.marking.isometryGroupCongr
              (toIsometry B _ (G.signedEquiv x)) ∧ P.sign x = (G.signedEquiv x).val.2 := by
  obtain ⟨G, hG⟩ := Q.exists_picardGroupEquivs_of_nodal_model href hE hprim hnef hsq
  exact ⟨G, hG, G.exists_root_free_cremonaComparison hE
    (hG.symm ▸ hprim) (hG.symm ▸ hnef) (hG.symm ▸ hsq)⟩

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
