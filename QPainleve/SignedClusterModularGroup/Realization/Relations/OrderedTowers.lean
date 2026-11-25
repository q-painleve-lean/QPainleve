/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Relations.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Surface.Boundary

import QPainleve.Algebra.Cluster.Word.SubtractionFree
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Family
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference

/-!
# Signed cluster relations from ordered blowup towers

One marked nodal contraction determines the order table for comparing signed cluster
loops in characteristic zero. The comparison extends the reference model using
`CompleteToricPresentation.exists_marked_family_of_nodal_model`. Specified ordered
toric and nodal blowup towers supply such a reference, retaining the original
surface, numbering and center labels.
-/

public section

open AlgebraicGeometry CategoryTheory Module Quiver
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "parameters[" c "]" => (fun j ↦ χ[c] (Multiplicative.ofAdd (Pi.single j 1)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {n r : ℕ} [NeZero n]

section Reference

variable {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)} (Q : CompleteToricPresentation i b r L γ)
  {c : Point Centers[r]} {M : MarkedSurface ℂ n B XTor[r]}

local instance instNonemptyOrderedTowersCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroOrderedTowersBoundaryLength : NeZero Q.length := Q.neZero
local instance instPrestableOrderedTowersToricBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) := Q.prestable

local notation "Fiber" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M

/-- For a primitive nef square-zero anticanonical cycle, the determinant orders of the
numbered surviving rays of a reference contraction give the complete integer relation
criterion over any characteristic-zero field. The reference center may have repeated
centers. -/
theorem CompleteToricPresentation.xPullback_eq_iff_signedLoopInvariants_eq_of_nodal_contraction
    (p₀ : Fiber) (hnodal₀ : p₀.IsNodalContraction)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M])))
    (hnef : (classOf(cartier[M])).IsNef ℂ (M.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M.surface classOf(cartier[M])
      classOf(cartier[M]) = 0)
    (k : Type*) [Field k] [CharZero k] (w v : Word E E)
    {d : ℕ} (β : Basis (Fin d) ℤ E.matrix.mulVecLin.ker) :
    let orders (j : Fin n) :=
      Fan.rayBoundaryOrders b Q.rays (p₀.numberedBoundaryRays cartier[M] (ZMod.finEquiv n j))
    w.xPullback k = v.xPullback k ↔
      w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) =
        v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) := by
  obtain ⟨F, hF, hreference, hfamily⟩ :=
    Q.exists_marked_family_of_nodal_model (Q.hasNodalModel_of_contraction hnodal₀) cartier[M]
  subst M
  choose p hp using fun z ↦ (hfamily z).1.exists_isNodalContraction cartier[F z]
  let P : ChargeSeed E N :=
    ⟨b.detDualEquiv.toLinearMap, Fan.rayChargeMap Q.rays, b.detDualEquiv_self, hE.symm⟩
  dsimp only
  rw [Path.xPullback_eq_iff_ySeed_coefficient_eq k w v,
    ← Path.xPullback_eq_iff_ySeed_coefficient_eq ℂ w v]
  exact GeometricRealization.xPullback_eq_iff_signedLoopInvariants_eq_of_presentation
    Q P rfl rfl F p₀ hnodal₀ (fun z _ ↦ p z) (fun z _ ↦ hp z)
    hnef hsq hprim (fun z j ↦ congrFun (hfamily z).2 j) Q.exists_cone_of_numbered_node w v β

end Reference

section OrderedTowers

variable {Φ : Fan i} {X W : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Scheme.IsRationalOver (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
  {m : ℕ} {T : BlowupTower X m W}

local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "Pic" => Additive (LineBundleClass X)
local notation "L" => Fin (Module.finrank ℤ Pic) → ℤ

local instance instIsIntegralOrderedTowersSurface : IsIntegral X := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  exact Scheme.IsRationalOver.isIntegral_of_smooth (f := X ↘ S) inferInstance

/-- Specified ordered toric and nodal blowup towers of a numbered primitive nef square-zero
anticanonical cycle supply a seed and a complete relation criterion. The order table is
the determinant table of the surviving rays in the original boundary numbering.
The fan and ray labels stay fixed. Transposing the frame to agree with the numbering
inverts all reference center parameters. -/
theorem exists_xPullback_eq_iff_signedLoopInvariants_eq_of_ordered_towers
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (s : Fin r → Φ.Ray) (u : Fin r → ℂˣ)
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).1 ≅ W)
    (hbase : e.hom ≫ T.toBase ≫ (X ↘ S) =
      (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).2.toTower.toBase ≫
        Φ.algebraicRealizationStructureMap)
    (hker : ((D.comap T.toBase).radical).comap e.hom =
      (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).2.boundaryι.ker)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD))) (hnef : classOf(hD).IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X classOf(hD) classOf(hD) = 0) :
    ∃ (H : LinearMap.BilinForm ℤ L) (μ : H.IsometryEquiv B)
      (b' : Basis (Fin 2) ℤ N) (Q : CompleteToricPresentation i b' r L Empty),
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∃ (c : Point Centers[r]) (f : X ⤏ XTor[r]) (E : SkewExchangeMatrix (Fin r)),
    let M := MarkedSurface.ofBoundary D A μ f
    ∃ p₀ : ContractedToricFiber b' Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M,
      p₀.IsNodalContraction ∧
      ((b' = b ∧ parameters[c] = u) ∨
        (b' = b.reindex (Equiv.swap 0 1) ∧ parameters[c] = u⁻¹)) ∧
      (∃ hfan : Q.fan = Φ, hfan ▸ Q.rays = s) ∧
      E.matrix = chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) ∧
      ∀ (k : Type*) [Field k] [CharZero k] (w v : Word E E)
        {d : ℕ} (β : Basis (Fin d) ℤ E.matrix.mulVecLin.ker),
        let orders (j : Fin n) := Fan.rayBoundaryOrders b' Q.rays
          (p₀.numberedBoundaryRays M.isEffectiveCartier_boundaryIdeal (ZMod.finEquiv n j))
        w.xPullback k = v.xPullback k ↔
          w.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) =
            v.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0) := by
  let : Module.Free ℤ Pic := X.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ Pic := X.finite_picard_of_isRationalOver ℂ
  let a : L ≃ₗ[ℤ] Pic := (Module.finBasis ℤ Pic).equivFun.symm
  let H := (B).comp a.toLinearMap a.toLinearMap
  let μ : H.IsometryEquiv B := ((B).isometryEquivOfCompLinearEquiv a).symm
  obtain ⟨b', Q, c, f, hframe, hrays, href⟩ :=
    exists_marked_reference_fiber_of_ordered_towers hΦ hc s u hT e hbase hker hD A μ
  let M := MarkedSurface.ofBoundary D A μ f
  let hD' := M.isEffectiveCartier_boundaryIdeal
  obtain ⟨p₀, hnodal₀⟩ := href.exists_isNodalContraction hD'
  have hδ : classOf(hD') = classOf(hD) :=
    congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr _ _
      (MarkedSurface.ofBoundary_ker D A μ f))
  let E : SkewExchangeMatrix (Fin r) :=
    .ofMatrix (chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
      (isSkewSymmetrizer_chargeExchangeMatrix _ b'.detDualEquiv_self _)
  have hE : E.matrix =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) :=
    SkewExchangeMatrix.matrix_ofMatrix _ _
  refine ⟨H, μ, b', Q, c, f, E, p₀, hnodal₀, hframe, hrays, hE, fun k _ _ w v _ β ↦ ?_⟩
  exact Q.xPullback_eq_iff_signedLoopInvariants_eq_of_nodal_contraction p₀ hnodal₀ hE
    (by rwa [hδ]) (by rwa [hδ]) (by rwa [hδ]) k w v β

end OrderedTowers

end QPainleve.SignedClusterModularGroup
