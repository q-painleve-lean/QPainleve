/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Twist
public import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction
public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over

/-!
# The Cartier connecting map and restriction of dual sections

For a Cartier divisor `D` and line bundles `M` and `W`, a section of the `W`-valued
dual of `M(-D)` gives a map `M(-D) ⟶ W` and its twist `M ⟶ W(D)`. Applying the
first map after the Cartier coboundary agrees with applying the Cartier coboundary
of `W(D)` after restricting the twisted map to `D`.

For the Cartier sequence on a point blowup, this is the compatibility of the
exceptional coboundary with evaluation by a restricted dual section before
taking the trace. The proof applies to any effective Cartier divisor and uses
the naturality of the long exact cohomology sequence.
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Scheme.Modules Scheme.Hom

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData) (R : Type u) [CommRing R]
  [X.Over (Spec (.of R))]

local notation "i" => I.subschemeι
local notation "F" => Scheme.Modules.pullback i

/-- The cohomology of the ideal-sheaf quotient of a line bundle is the cohomology of its
restriction to the closed subscheme. -/
def cohomologyTensorRestrictionEquiv (M : InvertibleSheaf X) (q : ℕ) :
    Cohomology (M.obj ⊗ I.pushforwardSubscheme) q ≃ₗ[R] Cohomology ((F).obj M.obj) q := by
  have := I.isIso_tensorRestrictionHom M
  exact (cohomologyBaseLinearEquivOfIso R (asIso (I.tensorRestrictionHom M)) q).trans
    ((i).cohomologyPushforwardBaseLinearEquiv R ((F).obj M.obj) q)

/-- The cohomology comparison takes the map on Cartier quotients to the actual pullback
of the line-bundle morphism. -/
theorem cohomologyTensorRestrictionEquiv_naturality {M N : InvertibleSheaf X}
    (a : M.obj ⟶ N.obj) (q : ℕ) (x : Cohomology (M.obj ⊗ I.pushforwardSubscheme) q) :
    I.cohomologyTensorRestrictionEquiv R N q
        (cohomologyMapBaseLinear R X (a ▷ I.pushforwardSubscheme) q x) =
      cohomologyMapBaseLinear R I.subscheme ((F).map a) q
        (I.cohomologyTensorRestrictionEquiv R M q x) := by
  simp only [cohomologyTensorRestrictionEquiv, LinearEquiv.trans_apply,
    cohomologyBaseLinearEquivOfIso_apply, asIso_hom]
  rw [← LinearMap.comp_apply, ← cohomologyMapBaseLinear_comp, tensorRestrictionHom_naturality,
    cohomologyMapBaseLinear_comp, LinearMap.comp_apply,
    Scheme.Hom.cohomologyPushforwardBaseLinearEquiv_naturality]

/-- The Cartier connecting map, with its domain written as cohomology on the closed
subscheme. -/
def cohomologyRestrictionConnecting (M : InvertibleSheaf X) (q : ℕ) :
    Cohomology ((F).obj M.obj) q →ₗ[R] Cohomology (M.obj ⊗ I.sheaf) (q + 1) :=
  (cohomologyδBaseLinear R X (I.shortExact_tensor_toPushforwardSubscheme M.obj) q (q + 1) rfl).comp
    (I.cohomologyTensorRestrictionEquiv R M q).symm.toLinearMap

/-- On an ambient quotient class the comparison recovers the original connecting map. -/
@[simp]
theorem cohomologyRestrictionConnecting_cohomologyTensorRestrictionEquiv
    (M : InvertibleSheaf X) (q : ℕ) (x : Cohomology (M.obj ⊗ I.pushforwardSubscheme) q) :
    I.cohomologyRestrictionConnecting R M q (I.cohomologyTensorRestrictionEquiv R M q x) =
      cohomologyδBaseLinear R X (I.shortExact_tensor_toPushforwardSubscheme M.obj) q (q + 1) rfl
        x := by
  simp [cohomologyRestrictionConnecting]

/-- The connecting map for a line bundle commutes with a morphism on the ambient twist
and its actual restriction to the closed subscheme. -/
theorem cohomologyRestrictionConnecting_naturality {M N : InvertibleSheaf X}
    (a : M.obj ⟶ N.obj) (q : ℕ) (x : Cohomology ((F).obj M.obj) q) :
    cohomologyMapBaseLinear R X (a ▷ I.sheaf) (q + 1)
        (I.cohomologyRestrictionConnecting R M q x) =
      I.cohomologyRestrictionConnecting R N q
        (cohomologyMapBaseLinear R I.subscheme ((F).map a) q x) := by
  obtain ⟨x, rfl⟩ := (I.cohomologyTensorRestrictionEquiv R M q).surjective x
  rw [← cohomologyTensorRestrictionEquiv_naturality,
    cohomologyRestrictionConnecting_cohomologyTensorRestrictionEquiv,
    cohomologyRestrictionConnecting_cohomologyTensorRestrictionEquiv]
  let S := ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme
  let φ : S.map (tensorLeft M.obj) ⟶ S.map (tensorLeft N.obj) :=
    S.mapNatTrans ((curriedTensor X.Modules).map a)
  simp only [coe_cohomologyMapBaseLinear, coe_cohomologyδBaseLinear]
  exact cohomologyδ_naturality (I.shortExact_tensor_toPushforwardSubscheme M.obj)
    (I.shortExact_tensor_toPushforwardSubscheme N.obj) φ q (q + 1) rfl x

variable {I}

/-- Evaluation of a dual section on the Cartier connecting class agrees with first
restricting the section to the divisor, then taking the connecting class of the
restricted product in the sequence of `W(D)`. -/
theorem IsEffectiveCartier.cohomologyMap_connecting_eq_of_dualRestriction
    (hI : I.IsEffectiveCartier) (M W : InvertibleSheaf X)
    (a : M.obj ⊗ I.sheaf ⟶ W.obj) (q : ℕ) (x : Cohomology ((F).obj M.obj) q) :
    cohomologyMapBaseLinear R X a (q + 1) (I.cohomologyRestrictionConnecting R M q x) =
      cohomologyMapBaseLinear R X (hI.tensorDualCancelIso W).hom (q + 1)
        (I.cohomologyRestrictionConnecting R (W.tensorProduct hI.toInvertibleSheaf.dual) q
          (cohomologyMapBaseLinear R I.subscheme
            ((F).map (hI.dualSectionTwist M.obj W a)) q x)) := by
  let b := hI.dualSectionTwist M.obj W a
  let c := (hI.tensorDualCancelIso W).hom
  let y := I.cohomologyRestrictionConnecting R M q x
  symm
  refine (congrArg (cohomologyMapBaseLinear R X c (q + 1))
    (I.cohomologyRestrictionConnecting_naturality R b q x).symm).trans ?_
  have hcomp := LinearMap.congr_fun
    (cohomologyMapBaseLinear_comp R X (b ▷ I.sheaf) c (q + 1)) y
  refine hcomp.symm.trans ?_
  exact congrArg (fun f ↦ cohomologyMapBaseLinear R X f (q + 1) y)
    (hI.dualSectionTwist_whiskerRight M.obj W a)

end AlgebraicGeometry.Scheme.IdealSheafData
