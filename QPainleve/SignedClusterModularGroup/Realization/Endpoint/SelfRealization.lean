/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Loop

import QPainleve.SignedClusterModularGroup.Realization.Closing

/-!
# Signed cluster loop realizations

Identify the endpoint of a signed word with the original toric presentation
at the reached centers. The marked Picard pullback and action on the numbered
branches are independent of the center. The branch orientation is given by
the inversion parity of the word.

The construction combines `GeometricRealization.exists_realize_signed_loop_with_oriented_refinement`
and `GeometricRealization.exists_comp_marked_toric_endpoint_comparison`.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap ℂ w P
local notation "Cnil[" P "]" => Quiver.Path.centerPartialMap ℂ Quiver.Path.nil P
local notation "src(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainSource (X := Centers[_]) (Y := Centers[_]) C
local notation "dst(" C "," c ")" =>
  c ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {γ : Type}

/-- A signed loop in a marked toric presentation of a primitive nef square-zero
anticanonical cycle realizes its independent X map between fibers of the same
presentation on the entire noncollision open. The orientation of its action on
the numbered branches equals the sign of the inversion count. The reached centers
carry nodal models of the original presentation. -/
theorem exists_realize_signed_loop
    {B : SkewExchangeMatrix (Fin r)} (w : Word B B) (P : ChargeSeed B N)
    (Q : CompleteToricPresentation i b r L γ)
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
    ∃ R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r])
        M M Cw[w,P] (w.xRationalMap ℂ),
      R.orientation = (-1 : ℤˣ) ^ w.inversionCount ∧ R.picard (d (R.boundaryPerm 0)) = d 0 ∧
      ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P],
        Q.HasNodalModel (dst(Cw[w,P],c)) (M (dst(Cw[w,P],c))) := by
  obtain ⟨γ', Q', M', R, -, hact, hmodels, e, hcharges, hdet, -, Δ, hΔQ', hΔΩ,
      hΔ, hpre, l, hlen, U, hleft, hright⟩ :=
    exists_realize_signed_loop_with_oriented_refinement
      w P Q hform hcharge M models hmodel (hD c₀) hnef hsq hcan hprim
  let := hpre
  let := hlen
  have hd : Function.Injective d := by
    rw [← funext (hmark c₀)]
    exact (M c₀).boundaryClass_injective_of_nef_square_zero (hD c₀) hnef hsq
  have hprop (c : Point Centers[r]) :=
    ((M c₀).primitive_nef_square_zero_iff_of_boundaryClass_eq (M c) (hD c₀) (hD c)
      (fun j ↦ (hmark c₀ j).trans (hmark c j).symm)).mp ⟨hprim, hnef, hsq⟩
  obtain ⟨_, T, -, hsign, -, hclass⟩ := exists_comp_marked_toric_endpoint_comparison
    Q' Q e hΔQ' hΔΩ R hΔ hcharges hdet U hleft hright
    (fun c ↦ (hmodels c).1) (fun c ↦ (hmodels c).2)
    (fun c ↦ hD (src(Cw[w,P],c))) (fun c ↦ hD (dst(Cw[w,P],c)))
    (fun c ↦ (hprop (src(Cw[w,P],c))).2.1) (fun c ↦ (hprop (dst(Cw[w,P],c))).2.1)
    (fun c ↦ (hprop (src(Cw[w,P],c))).2.2) (fun c ↦ (hprop (dst(Cw[w,P],c))).2.2)
    (d 0) d hd (fun c ↦ hmark (src(Cw[w,P],c)) 0) (fun c ↦ hmark (dst(Cw[w,P],c)))
  refine ⟨T, ?_, hclass, fun c ↦ (hmodels c).2⟩
  rw [hsign, R.orientation_def, hact, map_pow, cycleOrientationSign_sr]

end QPainleve.SignedClusterModularGroup.GeometricRealization
