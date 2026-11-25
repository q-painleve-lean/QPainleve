/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Conjugation.Signed
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization

import QPainleve.SignedClusterModularGroup.Realization.Anticanonical
import QPainleve.SignedClusterModularGroup.Realization.NodalFiber

/-!
# Conjugation between marked toric presentations

For a specified connecting word, the change of Picard marking is the pullback
of its geometric realization between the prescribed presentations. The
conjugation square holds on the independent X maps themselves, including for
odd connecting words and boundaries with at most two components.
The geometric comparison is `GeometricRealization.signedPicardHom_base_change`.
The unsigned square follows by including rotations and unsigned X maps.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cw[" w "," P "]" => Path.centerPartialMap ℂ w P
local notation "Cnil[" P "]" => Path.centerPartialMap ℂ Path.nil P
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "eval[" E "," w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))
local notation "Maps[" E "]" => (SignedClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "UnsignedMaps[" E "]" => (ClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "incl[" E "]" => MonoidHom.op (clusterModularGroupInclusion ℂ E)

variable {r n : ℕ} [NeZero n] {E₀ E₁ : SkewExchangeMatrix (Fin r)}
  {N₀ V₀ N₁ V₁ : Type} [AddCommGroup N₀] [AddCommGroup V₀] [Module ℝ V₀]
  [AddCommGroup N₁] [AddCommGroup V₁] [Module ℝ V₁]
  {i₀ : N₀ →+ V₀} {i₁ : N₁ →+ V₁} {b₀ : Basis (Fin 2) ℤ N₀} {b₁ : Basis (Fin 2) ℤ N₁}
  {L₀ L₁ γ₀ γ₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {H₀ : LinearMap.BilinForm ℤ L₀} {H₁ : LinearMap.BilinForm ℤ L₁}
  {M₀ : Point Centers[r] → MarkedSurface ℂ n H₀ XTor[r]}
  {M₁ : Point Centers[r] → MarkedSurface ℂ n H₁ XTor[r]}
  {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}
  {hD₀ : ∀ c, D[M₀ c].IsEffectiveCartier} {hD₁ : ∀ c, D[M₁ c].IsEffectiveCartier}
  {hmark₀ : ∀ c j, (M₀ c).boundaryClass (hD₀ c) j = d₀ j}
  {hmark₁ : ∀ c j, (M₁ c).boundaryClass (hD₁ c) j = d₁ j}

local notation "TargetModels[" basis "," Q "," M "," C "]" =>
  HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := basis)
    (hΦ := CompleteToricPresentation.regular Q) (T := CompleteToricPresentation.cycle Q)
    (origin := CompleteToricPresentation.origin Q) (s := CompleteToricPresentation.rays Q)
    (ι := CompleteToricPresentation.inclusion Q) (P₁ := M)
    (fun c : Point Centers[r] ↦ χ[c]) C

/-- The signed Picard equivalences of two marked toric presentations intertwine
conjugation by a specified connecting word and conjugation by its marked
pullback. The equivalences are characterized here by their values on loop
realizations on the canonical center domains. The branch sign of the
connecting realization is the inversion parity of the word. Its pullback
also intertwines the unsigned Picard equivalences compatible with the two
inclusions. -/
theorem exists_picardEquiv_base_change_of_presentations
    (w : Word E₀ E₁) (P₀ : ChargeSeed E₀ N₀) (P₁ : ChargeSeed E₁ N₁)
    (Q₀ : CompleteToricPresentation i₀ b₀ r L₀ γ₀)
    (Q₁ : CompleteToricPresentation i₁ b₁ r L₁ γ₁)
    (hform₀ : P₀.form = b₀.detDualEquiv.toLinearMap)
    (hcharge₀ : P₀.charge = Fan.rayChargeMap Q₀.rays)
    (hform₁ : P₁.form = b₁.detDualEquiv.toLinearMap)
    (hcharge₁ : P₁.charge = Fan.rayChargeMap Q₁.rays)
    (models₀ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₀],
      Q₀.HasNodalModel (dst(Cnil[P₀],c)) (M₀ (dst(Cnil[P₀],c))))
    (models₁ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₁],
      Q₁.HasNodalModel (dst(Cnil[P₁],c)) (M₁ (dst(Cnil[P₁],c))))
    {a₀ a₁ : Point Centers[r]} (href₀ : Q₀.HasNodalModel a₀ (M₀ a₀))
    (href₁ : Q₁.HasNodalModel a₁ (M₁ a₁))
    (hnef₀ : (classOf(hD₀ a₀)).IsNef ℂ ((M₀ a₀).surface ↘ S))
    (hnef₁ : (classOf(hD₁ a₁)).IsNef ℂ ((M₁ a₁).surface ↘ S))
    (hsq₀ : Chow.classIntersectionNumber ℂ (M₀ a₀).surface classOf(hD₀ a₀) classOf(hD₀ a₀) = 0)
    (hsq₁ : Chow.classIntersectionNumber ℂ (M₁ a₁).surface classOf(hD₁ a₁) classOf(hD₁ a₁) = 0)
    (hprim₀ : IsPrimitive (Additive.ofMul classOf(hD₀ a₀)))
    (hprim₁ : IsPrimitive (Additive.ofMul classOf(hD₁ a₁)))
    (Θ₀ : Maps[E₀] ≃* signedBoundaryIsometryGroup H₀ d₀)
    (Θ₁ : Maps[E₁] ≃* signedBoundaryIsometryGroup H₁ d₁)
    (hΘ₀ :
      letI := Q₀.complete.nonempty_cones
      letI := Q₀.prestable
      letI := Q₀.neZero
      ∀ (v : Word E₀ E₀) (A : GeometricRealization M₀ M₀ Cw[v,P₀] (v.xRationalMap ℂ)),
        TargetModels[b₀,Q₀,M₀,Cw[v,P₀]] →
          Θ₀ eval[E₀,v] = A.toSignedBoundaryIsometry d₀ hD₀ hmark₀)
    (hΘ₁ :
      letI := Q₁.complete.nonempty_cones
      letI := Q₁.prestable
      letI := Q₁.neZero
      ∀ (v : Word E₁ E₁) (A : GeometricRealization M₁ M₁ Cw[v,P₁] (v.xRationalMap ℂ)),
        TargetModels[b₁,Q₁,M₁,Cw[v,P₁]] →
          Θ₁ eval[E₁,v] = A.toSignedBoundaryIsometry d₁ hD₁ hmark₁) :
    ∃ R : GeometricRealization M₀ M₁ Cw[w,P₀] (w.xRationalMap ℂ),
      R.orientation = (-1 : ℤˣ) ^ w.inversionCount ∧
      (MulEquiv.op (signedClusterModularGroupCongr ℂ w)).trans Θ₁ =
        Θ₀.trans (R.signedBoundaryIsometryGroupCongr hmark₀ hmark₁) ∧
      ∀ (φ₀ : UnsignedMaps[E₀] ≃* boundaryRotationGroup H₀ d₀)
        (φ₁ : UnsignedMaps[E₁] ≃* boundaryRotationGroup H₁ d₁),
        (∀ x, SignedBoundaryIsometryGroup.rotationInclusion H₀ d₀ (φ₀ x) = Θ₀ (incl[E₀] x)) →
        (∀ x, SignedBoundaryIsometryGroup.rotationInclusion H₁ d₁ (φ₁ x) = Θ₁ (incl[E₁] x)) →
        (MulEquiv.op (clusterModularGroupCongr ℂ w)).trans φ₁ =
          φ₀.trans (R.boundaryRotationGroupCongr hmark₀ hmark₁) := by
  obtain ⟨R, hsign, -, hmodels⟩ := exists_realize_signed_word_to_presentation w P₀ P₁ Q₀ Q₁
    hform₀ hcharge₀ hform₁ hcharge₁ M₀ M₁ models₀ models₁ href₁ hD₀ hD₁
    hnef₀ hnef₁ hsq₀ hsq₁ hprim₀ hprim₁ d₀ d₁ hmark₀ hmark₁
  let := Q₁.complete.nonempty_cones
  let := Q₁.prestable
  let := Q₁.neZero
  let : PreirreducibleSpace Centers[r].left :=
    inferInstanceAs (PreirreducibleSpace (scheme ℂ (Fin r → ℤ)))
  let : IsRationalOver ((M₁ a₁).surface ↘ S) := href₁.isRationalOver
  have hcan₁ := congrArg Inv.inv (href₁.canonicalClass (hD₁ a₁))
  have hindex := Q₁.chargeIndex_ne_zero_of_anticanonical_cycle href₁
    (hD₁ a₁) hnef₁ hsq₁ hcan₁ hprim₁
  have hsigned := R.signedPicardHom_base_change
    (b := b₁) (hΦ := Q₁.regular) (T := Q₁.cycle) (origin := Q₁.origin)
    (s := Q₁.rays) (centers := fun c : Point Centers[r] ↦ χ[c])
    hmark₀ hmark₁ Q₁.complete (Q₁.inclusion_injective href₁) hindex
    (fun c ↦ (hmodels c).nonempty_contractedToricFiber) Θ₀.toMonoidHom Θ₁.toMonoidHom
    (fun v ↦ by
      obtain ⟨A, -, -, hA⟩ := exists_realize_signed_loop v P₀ Q₀
        hform₀ hcharge₀ M₀ models₀ href₀ hD₀ hnef₀ hsq₀ hprim₀ d₀ hmark₀
      exact ⟨Cw[v,P₀], inferInstance, inferInstance, A, hΘ₀ v A
        (fun c ↦ (hA c).nonempty_contractedToricFiber)⟩)
    (fun v ↦ by
      obtain ⟨A, -, -, hA⟩ := exists_realize_signed_loop v P₁ Q₁
        hform₁ hcharge₁ M₁ models₁ href₁ hD₁ hnef₁ hsq₁ hprim₁ d₁ hmark₁
      have htarget : TargetModels[b₁,Q₁,M₁,Cw[v,P₁]] :=
        fun c ↦ (hA c).nonempty_contractedToricFiber
      exact ⟨Cw[v,P₁], inferInstance, inferInstance, A, htarget, hΘ₁ v A htarget⟩)
  refine ⟨R, hsign, MulEquiv.toMonoidHom_injective hsigned, fun φ₀ φ₁ hφ₀ hφ₁ ↦ ?_⟩
  apply MulEquiv.ext
  intro x
  apply SignedBoundaryIsometryGroup.rotationInclusion_injective H₁ d₁
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hφ₁,
    ← R.signedBoundaryIsometryGroupCongr_rotationInclusion, hφ₀]
  have hx := DFunLike.congr_fun hsigned (incl[E₀] x)
  simpa only [MonoidHom.comp_apply, MonoidHom.op_apply_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.op_apply_apply, Function.comp_apply, unop_op, signedClusterModularGroupCongr_inclusion]
    using hx

end QPainleve.SignedClusterModularGroup.GeometricRealization
