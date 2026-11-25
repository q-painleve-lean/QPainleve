/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization
public import QPainleve.SignedClusterModularGroup.Realization.PicardAction

import QPainleve.Algebra.Cluster.ChargeKernel.Index
import QPainleve.Algebra.Cluster.Word.SignExtension

/-!
# The signed Picard action of a marked toric presentation

Closing signed loop realizations in a fixed marked toric presentation gives a Picard
pullback homomorphism on the opposite group of independent X maps. The target models
are supplied on the noncollision opens of the loop realizations. The sign of the
Picard action agrees with the descended inversion sign, whose kernel is the unsigned
group. The construction uses `GeometricRealization.exists_realize_signed_loop`
and `GeometricRealization.marked_actions_eq_of_xMap_eq`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite
open Module (Basis)
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "A[" r "]" => (Fin r → ℤ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ A[r])
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap ℂ w P
local notation "Cnil[" P "]" => Quiver.Path.centerPartialMap ℂ Quiver.Path.nil P
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "χ[" c "]" => pointsEquiv ℂ _
  (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "Loops[" E "]" => End (Prefunctor.obj (Paths.of (SkewExchangeMatrix (Fin _))) E)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {γ : Type}
  {E : SkewExchangeMatrix (Fin r)}

namespace GeometricRealization

local instance instIsDominantPresentationLoopXRationalMap (w : Loops[E]) :
    ((End.asHom w).xRationalMap ℂ).IsDominant :=
  Quiver.Path.instIsDominantXRationalMap ℂ (End.asHom w)

/-- The signed Picard pullback of a fixed marked toric presentation of a
primitive nef square-zero anticanonical cycle descends to the opposite signed
cluster modular group. It computes the marked action of every realization whose
reached centers have models in the presentation. The sign kernel on the point-map
group is the image of its unsigned subgroup. -/
theorem existsUnique_signedPicardHom_of_presentation
    (P : ChargeSeed E N) (Q : CompleteToricPresentation i b r L γ)
    (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
    (models : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P],
      Q.HasNodalModel (dst(Cnil[P],c)) (M (dst(Cnil[P],c))))
    {c₀ : Point Centers[r]} (hmodel : Q.HasNodalModel c₀ (M c₀))
    [IsRationalOver ((M c₀).surface ↘ S)]
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    (hnef : (classOf(hD c₀)).IsNef ℂ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hcan : letI : SmoothOfRelativeDimension 2 ((M c₀).surface ↘ S) := (M c₀).smooth
      classOf(hD c₀) = (LineBundleClass.mk (canonicalBundle ℂ (M c₀).surface 2))⁻¹)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (d : ZMod n → L) (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∃! ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup H d,
      (∀ (w : Loops[E]),
        SignedBoundaryIsometryGroup.sign H d (ρ (op (signedClusterModularGroupMap ℂ E w))) =
          (-1 : ℤˣ) ^ (End.asHom w).inversionCount ∧
        ∀ {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
          [C.IsOver Centers[r].hom Centers[r].hom]
          (R : GeometricRealization M M C ((End.asHom w).xRationalMap ℂ)),
          HasToricTargetModels (b := b) (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin)
            (s := Q.rays) (ι := Q.inclusion) (P₁ := M) (fun c : Point Centers[r] ↦ χ[c]) C →
          ρ (op (signedClusterModularGroupMap ℂ E w)) =
            R.toSignedBoundaryIsometry d hD hmark) ∧
      ((SignedBoundaryIsometryGroup.sign H d).comp ρ).ker.unop =
        (clusterModularGroupInclusion ℂ E).range := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  have hindex := Q.chargeIndex_ne_zero_of_anticanonical_cycle (M := M) hmodel
    (hD c₀) hnef hsq hcan hprim
  let : PreirreducibleSpace Centers[r].left :=
    inferInstanceAs (PreirreducibleSpace (scheme ℂ A[r]))
  obtain ⟨ρ, hρ, huniq⟩ :=
    existsUnique_signedPicardHom_of_realizations (E := E) d hD hmark Q.complete
      (Q.inclusion_injective hmodel) hindex (centers := fun c : Point Centers[r] ↦ χ[c]) (by
        intro w
        let word : Word E E := End.asHom w
        obtain ⟨R, hη, _, hmodels⟩ := exists_realize_signed_loop word P Q
          hform hcharge M models hmodel hD hnef hsq hprim d hmark
        have hdom : IsDominant Cw[word,P].hom := inferInstance
        have hover : Cw[word,P].IsOver Centers[r].hom Centers[r].hom := inferInstance
        exact ⟨Cw[word,P], hdom, hover, R, hη, fun c ↦ (hmodels c).nonempty_contractedToricFiber⟩)
  refine ⟨ρ, ⟨hρ, ?_⟩, fun ρ' hρ' ↦ huniq ρ' hρ'.1⟩
  have hE : E.matrix ≠ 0 := by
    intro hzero
    have hmat : chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays) = 0 := by
      rw [← hcharge, ← hform, P.matrix_eq, hzero]
    apply hindex
    rw [(Fan.rayChargeMap Q.rays).index_range_eq_gcd_chargeExchangeMatrix b
      b.detDualEquiv_self b.detDualEquiv_apply_basis_zero_one, Finset.gcd_eq_zero_iff]
    intro j _
    simp only [hmat, Matrix.zero_apply, Int.natAbs_zero]
  rw [range_clusterModularGroupInclusion ℂ E hE]
  ext g
  obtain ⟨w, rfl⟩ := signedClusterModularGroupMap_surjective ℂ E g
  simp only [Subgroup.mem_unop, MonoidHom.mem_ker, MonoidHom.comp_apply, (hρ w).1,
    signedInversionSign_apply]

end GeometricRealization

end QPainleve.SignedClusterModularGroup
