/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.LinearAlgebra.BilinearForm.Conjugation
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Group
public import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.SignedClusterModularGroup.Boundary.Conjugation
import QPainleve.SignedClusterModularGroup.Realization.Surface.PrimeClass

/-!
# Cluster modular groups of numbered surface presentations

Specified nodal and internal blowup towers determine the seed and the Picard
group identifications of the original numbered surface. A finite integral
marking supplies the moving family, and conjugation by that marking recovers
the group on the actual Picard lattice. The oriented toric basis is chosen by
`exists_marked_reference_fiber_of_ordered_towers`, and the identifications are
given by `CompleteToricPresentation.exists_picardGroupEquivs_of_nodal_model`.
-/

public section

open AlgebraicGeometry CategoryTheory Module MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster
open QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "δ[" h "]" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "ideal[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "parameters[" c "]" => (fun j ↦ χ[c] (Multiplicative.ofAdd (Pi.single j 1)))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N}
  {X : Scheme} [X.Over S] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [Scheme.IsRationalOver (X ↘ S)]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
  {n r : ℕ} [NeZero n]

local instance : IsIntegral X := by
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  exact Scheme.IsRationalOver.isIntegral_of_smooth (f := X ↘ S) inferInstance

local notation "Pic" => Additive (LineBundleClass X)
local notation "L" => (Fin (Module.finrank ℤ Pic) → ℤ)
local notation "B" => Chow.intersectionBilinForm ℂ X
local notation "classes[" A "," hD "]" =>
  (fun j ↦ Additive.ofMul (LineBundleClass.primeDivisorClass
    (D.boundaryPrimeEmbedding (Scheme.NodalCycleNumbering.boundaryPrimeEquiv A hD j))))

local notation "Models[" b₀ "," Q "," M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b₀)
    (s := CompleteToricPresentation.rays Q)
    (hΦ := CompleteToricPresentation.regular Q) (T := CompleteToricPresentation.cycle Q)
    (origin := CompleteToricPresentation.origin Q) (ι := CompleteToricPresentation.inclusion Q)
    (P₁ := M) (fun z : Point Centers[r] ↦ χ[z]) C

/-- For a specified ordered toric presentation of a primitive nef square-zero
anticanonical cycle, the signed and unsigned opposite cluster modular groups
identify with the signed boundary isometries and rotations of the original
Picard group. The reference family keeps the original surface and numbering.
The oriented frame retains the input fan and all ray labels, and in the
transposed frame the reference center parameters are inverted. The signed
equivalence evaluates by geometric Picard pullback and the branch sign. -/
theorem exists_picardGroupEquivs_of_toric_presentation
    (P : D.ToricPresentation (X ↘ S) b i r)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (hD : D.IsEffectiveCartier)
    (hprim : IsPrimitive (Additive.ofMul δ[hD])) (hnef : δ[hD].IsNef ℂ (X ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ X δ[hD] δ[hD] = 0) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
    letI := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let d := classes[A,hD]
    ∃ (H : LinearMap.BilinForm ℤ L) (μ : H.IsometryEquiv B)
      (b' : Basis (Fin 2) ℤ N) (Q : CompleteToricPresentation i b' r L Empty),
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∃ (c : Point Centers[r]) (f : X ⤏ XTor[r]) (E : SkewExchangeMatrix (Fin r))
      (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
      (hD' : ∀ z, ideal[M z].IsEffectiveCartier)
      (Θ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ ≃* signedBoundaryIsometryGroup B d)
      (Θrot : (ClusterModularGroup ℂ E)ᵐᵒᵖ ≃* boundaryRotationGroup B d),
      ((b' = b ∧ parameters[c] = P.parameters) ∨
        (b' = b.reindex (Equiv.swap 0 1) ∧ parameters[c] = P.parameters⁻¹)) ∧
      (∃ hfan : Q.fan = P.fan, hfan ▸ Q.rays = P.rays) ∧
      E.matrix = chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) ∧
      M c = MarkedSurface.ofBoundary D A μ f ∧ (∀ z, Q.HasNodalModel z (M z)) ∧
      (∀ z j, (M z).boundaryClass (hD' z) j = μ.symm (d j)) ∧
      (∀ (w : Word E E),
        sign B d (Θ (op (signedClusterModularGroupMap ℂ E (End.of w)))) =
          (-1 : ℤˣ) ^ w.inversionCount ∧
        ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C (w.xRationalMap ℂ)),
          Models[b',Q,M,C] →
          (Θ (op (signedClusterModularGroupMap ℂ E (End.of w)))).val =
            (μ.isometryGroupCongr (H.isometryGroupEquivIsometryEquiv.symm R.picard),
              R.orientation)) ∧
      ((sign B d).comp Θ.toMonoidHom).ker.unop = (clusterModularGroupInclusion ℂ E).range ∧
      (∀ x, rotationInclusion B d (Θrot x) =
        Θ (MonoidHom.op (clusterModularGroupInclusion ℂ E) x)) := by
  let : Module.Free ℤ Pic := X.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ Pic := X.finite_picard_of_isRationalOver ℂ
  let a : L ≃ₗ[ℤ] Pic := (Module.finBasis ℤ Pic).equivFun.symm
  let H := (B).comp a.toLinearMap a.toLinearMap
  let μ : H.IsometryEquiv B := ((B).isometryEquivOfCompLinearEquiv a).symm
  obtain ⟨b', Q, c, f, hframe, hrays, href⟩ :=
    exists_marked_reference_fiber_of_ordered_towers P.regular P.complete P.rays P.parameters
      P.isNodal P.iso P.iso_over P.iso_boundary hD A μ
  let M₀ := MarkedSurface.ofBoundary D A μ f
  have hδ : δ[M₀.isEffectiveCartier_boundaryIdeal] = δ[hD] :=
    congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr _ _
      (MarkedSurface.ofBoundary_ker D A μ f))
  let E : SkewExchangeMatrix (Fin r) :=
    .ofMatrix (chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
      (isSkewSymmetrizer_chargeExchangeMatrix _ b'.detDualEquiv_self _)
  have hE : E.matrix =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) :=
    SkewExchangeMatrix.matrix_ofMatrix _ _
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let d := classes[A,hD]
  have hd : M₀.boundaryClass M₀.isEffectiveCartier_boundaryIdeal = μ.symm ∘ d :=
    funext (MarkedSurface.boundaryClass_ofBoundary D A μ f hD)
  have hgroups := Q.exists_picardGroupEquivs_of_nodal_model (M₀ := M₀) href hE
    (by rwa [hδ]) (by rwa [hδ]) (by rwa [hδ])
  dsimp only at hgroups
  rw [hd] at hgroups
  obtain ⟨M, hD', hmark, Θ, Θrot, hM, hmodels, hwords, hsign, hrot⟩ := hgroups
  have hmatch (j : ZMod n) : μ.symm (d j) = (μ.symm ∘ d) ((1 : ℤˣ) • j + 0) := by simp
  let α := SignedBoundaryIsometryGroup.congr μ.symm hmatch
  let β := boundaryRotationGroupCongr μ.symm hmatch
  have hcomp : (sign B d).comp (Θ.trans α).toMonoidHom =
      (sign H (μ.symm ∘ d)).comp Θ.toMonoidHom :=
    MonoidHom.ext fun x ↦ by
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply,
        α, SignedBoundaryIsometryGroup.sign_apply, coe_congr]
  refine ⟨H, μ, b', Q, c, f, E, M, hD', Θ.trans α, Θrot.trans β,
    hframe, hrays, hE, hM, hmodels, hmark, ?_, ?_, ?_⟩
  · intro w
    refine ⟨(DFunLike.congr_fun hcomp _).trans (hwords w).1, fun R hR ↦ ?_⟩
    simp only [MulEquiv.trans_apply, α, coe_congr, (hwords w).2 R hR, coe_toSignedBoundaryIsometry]
    rfl
  · rw [hcomp, hsign]
  · intro x
    simpa only [MulEquiv.trans_apply, α, β, congr_rotationInclusion] using
      congrArg α (hrot x)

end QPainleve.SignedClusterModularGroup
