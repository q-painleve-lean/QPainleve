/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.ConnectingWord

/-!
# Signed cluster loop realizations

Identify the endpoint of a signed word with the original toric presentation
at the reached centers. The marked Picard pullback and action on the numbered
branches are independent of the center. The branch orientation is given by
the inversion parity of the word.

Both ends use the same presentation and numerical data in
`GeometricRealization.exists_realize_signed_word_to_presentation`.
-/

public section

open AlgebraicGeometry CategoryTheory Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "Cw[" w "," P "]" => Quiver.Path.centerPartialMap k₀ w P
local notation "Cnil[" P "]" => Quiver.Path.centerPartialMap k₀ Quiver.Path.nil P
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
    (Q : CompleteToricPresentation k₀ i b r L γ)
    (hform : P.form = b.detDualEquiv.toLinearMap)
    (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (M : Point Centers[r] → MarkedSurface k₀ n H XTor[r])
    (models : ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cnil[P],
      Q.HasNodalModel (dst(Cnil[P],c)) (M (dst(Cnil[P],c))))
    {c₀ : Point Centers[r]} (hmodel : Q.HasNodalModel c₀ (M c₀))
    (hD : ∀ c, D[M c].IsEffectiveCartier)
    (hnef : (classOf(hD c₀)).IsNef k₀ ((M c₀).surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ (M c₀).surface classOf(hD c₀) classOf(hD c₀) = 0)
    (hprim : IsPrimitive (Additive.ofMul classOf(hD c₀)))
    (d : ZMod n → L) (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j) :
    ∃ R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r])
        M M Cw[w,P] (w.xRationalMap k₀),
      R.orientation = (-1 : ℤˣ) ^ w.inversionCount ∧ R.picard (d (R.boundaryPerm 0)) = d 0 ∧
      ∀ c : CenterPoint (U := Centers[r]) (V := Centers[r]) Cw[w,P],
        Q.HasNodalModel (dst(Cw[w,P],c)) (M (dst(Cw[w,P],c))) :=
  exists_realize_signed_word_to_presentation w P P Q Q hform hcharge hform hcharge
    M M models models hmodel hD hD hnef hnef hsq hsq hprim hprim d d hmark hmark

end QPainleve.SignedClusterModularGroup.GeometricRealization
