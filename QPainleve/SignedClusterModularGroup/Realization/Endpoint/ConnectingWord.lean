/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Refinement

import QPainleve.SignedClusterModularGroup.Realization.Closing

/-!
# Signed words between marked toric presentations

A connecting word between two seeds is realized between their specified
presentations. Its transported model is compared with the chosen target model
on an oriented common refinement. The resulting pullback gives the change of
Picard marking for conjugation by the word, with the sign on ordered branches
retained for every cycle length. The endpoint comparison uses
`GeometricRealization.exists_comp_marked_toric_endpoint_comparison`.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cw[" w "," P "]" => Path.centerPartialMap k₀ w P
local notation "Cnil[" P "]" => Path.centerPartialMap k₀ Path.nil P
local notation "src(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainSource (X := Centers[_]) (Y := Centers[_]) C
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C

variable {N₀ V₀ N₁ V₁ : Type} [AddCommGroup N₀] [AddCommGroup V₀] [Module ℝ V₀]
  [AddCommGroup N₁] [AddCommGroup V₁] [Module ℝ V₁]
  {i₀ : N₀ →+ V₀} {i₁ : N₁ →+ V₁} {b₀ : Basis (Fin 2) ℤ N₀} {b₁ : Basis (Fin 2) ℤ N₁}
  {r n : ℕ} [NeZero n] {L₀ L₁ γ₀ γ₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {H₀ : LinearMap.BilinForm ℤ L₀} {H₁ : LinearMap.BilinForm ℤ L₁}
  {B E : SkewExchangeMatrix (Fin r)}

/-- A specified signed word realizes the independent X map between two ordered
toric presentations of primitive nef square-zero anticanonical cycles. The
realization is defined on the word's whole noncollision open, and the reached
centers have nodal models of the prescribed target. Its ordered branch sign is
the inversion parity, and the pullback takes the image of boundary component zero
back to its source class. The reference centers can lie outside the open. -/
theorem exists_realize_signed_word_to_presentation
    (w : Word B E) (P₀ : ChargeSeed B N₀) (P₁ : ChargeSeed E N₁)
    (Q₀ : CompleteToricPresentation k₀ i₀ b₀ r L₀ γ₀)
    (Q₁ : CompleteToricPresentation k₀ i₁ b₁ r L₁ γ₁)
    (hform₀ : P₀.form = b₀.detDualEquiv.toLinearMap)
    (hcharge₀ : P₀.charge = Fan.rayChargeMap Q₀.rays)
    (hform₁ : P₁.form = b₁.detDualEquiv.toLinearMap)
    (hcharge₁ : P₁.charge = Fan.rayChargeMap Q₁.rays)
    (M₀ : Point Centers[r] → MarkedSurface k₀ n H₀ XTor[r])
    (M₁ : Point Centers[r] → MarkedSurface k₀ n H₁ XTor[r])
    (models₀ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₀],
      Q₀.HasNodalModel (dst(Cnil[P₀],c)) (M₀ (dst(Cnil[P₀],c))))
    (models₁ : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P₁],
      Q₁.HasNodalModel (dst(Cnil[P₁],c)) (M₁ (dst(Cnil[P₁],c))))
    {a₀ a₁ : Point Centers[r]} (href₁ : Q₁.HasNodalModel a₁ (M₁ a₁))
    (hD₀ : ∀ c, D[M₀ c].IsEffectiveCartier) (hD₁ : ∀ c, D[M₁ c].IsEffectiveCartier)
    (hnef₀ : (classOf(hD₀ a₀)).IsNef k₀ ((M₀ a₀).surface ↘ S))
    (hnef₁ : (classOf(hD₁ a₁)).IsNef k₀ ((M₁ a₁).surface ↘ S))
    (hsq₀ : Chow.classIntersectionNumber k₀ (M₀ a₀).surface classOf(hD₀ a₀) classOf(hD₀ a₀) = 0)
    (hsq₁ : Chow.classIntersectionNumber k₀ (M₁ a₁).surface classOf(hD₁ a₁) classOf(hD₁ a₁) = 0)
    (hprim₀ : IsPrimitive (Additive.ofMul classOf(hD₀ a₀)))
    (hprim₁ : IsPrimitive (Additive.ofMul classOf(hD₁ a₁)))
    (d₀ : ZMod n → L₀) (d₁ : ZMod n → L₁)
    (hmark₀ : ∀ c j, (M₀ c).boundaryClass (hD₀ c) j = d₀ j)
    (hmark₁ : ∀ c j, (M₁ c).boundaryClass (hD₁ c) j = d₁ j) :
    ∃ R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r])
        M₀ M₁ Cw[w,P₀] (w.xRationalMap k₀),
      R.orientation = (-1 : ℤˣ) ^ w.inversionCount ∧ R.picard (d₁ (R.boundaryPerm 0)) = d₀ 0 ∧
      ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P₀],
        Q₁.HasNodalModel (dst(Cw[w,P₀],c)) (M₁ (dst(Cw[w,P₀],c))) := by
  obtain ⟨_, Q, _, A, -, hact, hmodels, e, hcharges, hdet, -, _, hΔQ, hΔΩ,
      hΔ, hpre, _, hlen, U, hleft, hright⟩ :=
    exists_realize_signed_word_with_oriented_refinement w P₀ P₁ Q₀ Q₁ hform₀ hcharge₀
      hform₁ hcharge₁ M₀ M₁ models₀ models₁ href₁ (hD₁ a₁) hnef₁ hsq₁ hprim₁
  let := hpre
  let := hlen
  have hd₁ : Function.Injective d₁ := by
    rw [← funext (hmark₁ a₁)]
    exact (M₁ a₁).boundaryClass_injective_of_nef_square_zero (hD₁ a₁) hnef₁ hsq₁
  have hprop₀ (c : Point Centers[r]) :=
    ((M₀ a₀).primitive_nef_square_zero_iff_of_boundaryClass_eq (M₀ c) (hD₀ a₀) (hD₀ c)
      (fun j ↦ (hmark₀ a₀ j).trans (hmark₀ c j).symm)).mp ⟨hprim₀, hnef₀, hsq₀⟩
  have hprop₁ (c : Point Centers[r]) :=
    ((M₁ a₁).primitive_nef_square_zero_iff_of_boundaryClass_eq (M₁ c) (hD₁ a₁) (hD₁ c)
      (fun j ↦ (hmark₁ a₁ j).trans (hmark₁ c j).symm)).mp ⟨hprim₁, hnef₁, hsq₁⟩
  obtain ⟨_, R, -, hsign, -, hclass⟩ := exists_comp_marked_toric_endpoint_comparison
    Q Q₁ e hΔQ hΔΩ A hΔ hcharges hdet U hleft hright
    (fun c ↦ (hmodels c).1) (fun c ↦ (hmodels c).2)
    (fun c ↦ hD₀ (src(Cw[w,P₀],c))) (fun c ↦ hD₁ (dst(Cw[w,P₀],c)))
    (fun c ↦ (hprop₀ (src(Cw[w,P₀],c))).2.1) (fun c ↦ (hprop₁ (dst(Cw[w,P₀],c))).2.1)
    (fun c ↦ (hprop₀ (src(Cw[w,P₀],c))).2.2) (fun c ↦ (hprop₁ (dst(Cw[w,P₀],c))).2.2)
    (d₀ 0) d₁ hd₁ (fun c ↦ hmark₀ (src(Cw[w,P₀],c)) 0) (fun c ↦ hmark₁ (dst(Cw[w,P₀],c)))
  refine ⟨R, ?_, hclass, fun c ↦ (hmodels c).2⟩
  rw [hsign, A.orientation_def, hact, map_pow, cycleOrientationSign_sr]

end QPainleve.SignedClusterModularGroup.GeometricRealization
