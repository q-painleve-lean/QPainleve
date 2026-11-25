/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.CartierPairing
public import QPainleve.AlgebraicGeometry.Cohomology.TracePairing

/-!
# Descent of trace duality along a Cartier sequence

The trace induced on an effective Cartier divisor is the ambient trace composed with
the Cartier connecting map for the positively twisted trace bundle. If the ambient
pairing for `M(-D)` and the induced pairing for `M|D` are perfect, then the pairing
for `M` is perfect in degrees in which the cohomology of `M|D` vanishes. The argument
identifies the dual of the cohomology quotient with the sections vanishing on the divisor.
The adjoint identity uses `IsEffectiveCartier.cohomologyMap_connecting_eq_of_dualRestriction`.
-/

public noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData} (R : Type u) [CommRing R]
  [X.Over (Spec (.of R))]

local notation "i" => I.subschemeι
local notation "F" => Scheme.Modules.pullback i
local notation "incl[" M "]" => tensorIdealInclusion I M
local notation "twist[" hI ", " W "]" =>
  InvertibleSheaf.tensorProduct W (InvertibleSheaf.dual (IsEffectiveCartier.toInvertibleSheaf hI))

variable (hI : I.IsEffectiveCartier)

/-- The trace on the restricted twist is induced by the Cartier connecting map and
the identification `W(D)(-D) ≅ W`. -/
def IsEffectiveCartier.cohomologyRestrictionTrace (W : InvertibleSheaf X) (q : ℕ)
    (tr : Cohomology W.obj (q + 1) →ₗ[R] R) :
    Cohomology ((F).obj (twist[hI, W]).obj) q →ₗ[R] R :=
  tr.comp ((cohomologyMapBaseLinear R X (hI.tensorDualCancelIso W).hom (q + 1)).comp
    (I.cohomologyRestrictionConnecting R (twist[hI, W]) q))

/-- Evaluate the induced trace by taking the connecting class in the Cartier sequence
for `W(D)`, identifying the result with a class of `W`, and applying the ambient trace. -/
@[simp]
theorem IsEffectiveCartier.cohomologyRestrictionTrace_apply (W : InvertibleSheaf X) (q : ℕ)
    (tr : Cohomology W.obj (q + 1) →ₗ[R] R)
    (x : Cohomology ((F).obj (twist[hI, W]).obj) q) :
    hI.cohomologyRestrictionTrace R W q tr x =
      tr (cohomologyMapBaseLinear R X (hI.tensorDualCancelIso W).hom (q + 1)
        (I.cohomologyRestrictionConnecting R (twist[hI, W]) q x)) :=
  (rfl)

/-- The Cartier connecting map is adjoint to restriction of twisted dual sections
for the induced trace. -/
theorem IsEffectiveCartier.cohomologyTracePairing_connecting (M W : InvertibleSheaf X) (q : ℕ)
    (tr : Cohomology W.obj (q + 1) →ₗ[R] R)
    (x : Cohomology ((F).obj M.obj) q)
    (s : Γ((ihom (M.obj ⊗ I.sheaf)).obj W.obj, ⊤)) :
    cohomologyTracePairing R (q + 1) tr (I.cohomologyRestrictionConnecting R M q x) s =
      cohomologyTracePairing R q (hI.cohomologyRestrictionTrace R W q tr) x
        (internalHomSectionsEquiv.symm
          ((F).map (hI.dualSectionTwist M.obj W (internalHomSectionsEquiv s)))) := by
  simp only [cohomologyTracePairing_apply, Equiv.apply_symm_apply,
    IsEffectiveCartier.cohomologyRestrictionTrace_apply]
  exact congrArg tr (hI.cohomologyMap_connecting_eq_of_dualRestriction R M W _ q x)

variable {k : Type u} [Field k] [X.Over (Spec (.of k))]

private theorem exact_cohomologyRestrictionConnecting_inclusion (M : InvertibleSheaf X)
    (q : ℕ) :
    Function.Exact (I.cohomologyRestrictionConnecting k M q)
      (cohomologyMapBaseLinear k X incl[M.obj] (q + 1)) := by
  let S := (ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).map (tensorLeft M.obj)
  have hS : S.ShortExact := I.shortExact_tensor_toPushforwardSubscheme M.obj
  intro x
  rw [tensorIdealInclusion_def, cohomologyMapBaseLinear_comp, LinearMap.comp_apply,
    ← cohomologyBaseLinearEquivOfIso_apply,
    ← map_zero (cohomologyBaseLinearEquivOfIso k (ρ_ M.obj) (q + 1)),
    (cohomologyBaseLinearEquivOfIso k (ρ_ M.obj) (q + 1)).injective.eq_iff]
  rw [congrFun (coe_cohomologyMapBaseLinear k X (M.obj ◁ I.sheafι) (q + 1)) x]
  refine (exact_cohomologyδ_cohomologyMap hS q (q + 1) rfl x).trans ?_
  simp only [← coe_cohomologyδBaseLinear k X hS]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨I.cohomologyTensorRestrictionEquiv k M q y, ?_⟩
    rw [cohomologyRestrictionConnecting_cohomologyTensorRestrictionEquiv]
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := (I.cohomologyTensorRestrictionEquiv k M q).surjective y
    refine ⟨z, ?_⟩
    rw [cohomologyRestrictionConnecting_cohomologyTensorRestrictionEquiv]

private theorem surjective_cohomologyMapBaseLinear_inclusion (M : InvertibleSheaf X) (n : ℕ)
    (hvan : Subsingleton (Cohomology ((F).obj M.obj) n)) :
    Function.Surjective (cohomologyMapBaseLinear k X incl[M.obj] n) := by
  let S := (ShortComplex.mk _ _ I.sheafι_toPushforwardSubscheme).map (tensorLeft M.obj)
  have hS : S.ShortExact := I.shortExact_tensor_toPushforwardSubscheme M.obj
  have hsub : Subsingleton (Cohomology (M.obj ⊗ I.pushforwardSubscheme) n) :=
    @Function.Injective.subsingleton _ _ _
      (I.cohomologyTensorRestrictionEquiv k M n).injective hvan
  have hsurj : Function.Surjective (cohomologyMapBaseLinear k X S.f n) := by
    intro y
    obtain ⟨x, hx⟩ := (exact_cohomologyMap_cohomologyMap hS n y).mp (hsub.allEq _ _)
    exact ⟨x, (congrFun (coe_cohomologyMapBaseLinear k X S.f n) x).trans hx⟩
  have hf : S.f = M.obj ◁ I.sheafι := rfl
  have hunit :
      Function.Surjective (cohomologyMapBaseLinear k X (ρ_ M.obj).hom n) := by
    have he := (cohomologyBaseLinearEquivOfIso k (ρ_ M.obj) n).surjective
    intro y
    obtain ⟨x, hx⟩ := he y
    exact ⟨x, (cohomologyBaseLinearEquivOfIso_apply k (ρ_ M.obj) n x).symm.trans hx⟩
  rw [tensorIdealInclusion_def, cohomologyMapBaseLinear_comp, ← hf]
  exact hunit.comp hsurj

/-- A perfect ambient pairing for the smaller twist descends to a perfect pairing
for the larger twist if the divisor pairing is perfect and the next cohomology
of the restricted line bundle vanishes. -/
theorem IsEffectiveCartier.isPerfPair_cohomologyTracePairing_of_cartier_twist
    (M W : InvertibleSheaf X) (q : ℕ) (tr : Cohomology W.obj (q + 1) →ₗ[k] k)
    [FiniteDimensional k (Cohomology M.obj (q + 1))]
    (hvan : Subsingleton (Cohomology ((F).obj M.obj) (q + 1)))
    (hamb : (cohomologyTracePairing (M := M.obj ⊗ I.sheaf) k (q + 1) tr).IsPerfPair)
    (hres : (cohomologyTracePairing (M := (F).obj M.obj) k q
      (hI.cohomologyRestrictionTrace k W q tr)).IsPerfPair) :
    (cohomologyTracePairing (M := M.obj) k (q + 1) tr).IsPerfPair := by
  let f := cohomologyMapBaseLinear k X incl[M.obj] (q + 1)
  let p := cohomologyTracePairing (M := M.obj) k (q + 1) tr
  let prev := cohomologyTracePairing (M := M.obj ⊗ I.sheaf) k (q + 1) tr
  have hsurj : Function.Surjective f := surjective_cohomologyMapBaseLinear_inclusion M _ hvan
  have hcomm (s : Γ((ihom M.obj).obj W.obj, ⊤)) (x : Cohomology (M.obj ⊗ I.sheaf) (q + 1)) :
      p (f x) s = prev x
        (internalHomSectionsEquiv.symm (incl[M.obj] ≫ internalHomSectionsEquiv s)) := by
    simp only [p, prev, f, cohomologyTracePairing_apply, Equiv.apply_symm_apply,
      cohomologyMapBaseLinear_comp, LinearMap.comp_apply]
  apply (LinearMap.IsPerfPair.of_bijective p.flip ?_).flip
  constructor
  · intro s₁ s₂ h
    apply internalHomSectionsEquiv.injective
    apply hI.injective_precomp_inclusion M.obj W
    rw [← Equiv.apply_eq_iff_eq internalHomSectionsEquiv.symm]
    apply hamb.bijective_right.injective
    ext x
    rw [LinearMap.flip_apply, LinearMap.flip_apply, ← hcomm, ← hcomm]
    exact DFunLike.congr_fun h (f x)
  · intro φ
    obtain ⟨s, hs⟩ := hamb.bijective_right.surjective (φ.comp f)
    let a := internalHomSectionsEquiv s
    let sD := internalHomSectionsEquiv.symm ((F).map (hI.dualSectionTwist M.obj W a))
    have hsD : sD = 0 := by
      apply hres.separatingRight
      intro x
      rw [← hI.cohomologyTracePairing_connecting k M W q tr x s]
      have hδ :=
        (exact_cohomologyRestrictionConnecting_inclusion (k := k) M q).apply_apply_eq_zero x
      simpa only [LinearMap.flip_apply, LinearMap.comp_apply, f, hδ, map_zero] using
        DFunLike.congr_fun hs (I.cohomologyRestrictionConnecting k M q x)
    have ha : (F).map (hI.dualSectionTwist M.obj W a) = 0 := by
      simpa only [sD, Equiv.apply_symm_apply, internalHomSectionsEquiv_zero] using
        congrArg internalHomSectionsEquiv hsD
    obtain ⟨b, hb⟩ := (hI.pullback_dualSectionTwist_eq_zero_iff M.obj W a).mp ha
    refine ⟨internalHomSectionsEquiv.symm b, ?_⟩
    ext y
    obtain ⟨x, rfl⟩ := hsurj y
    rw [LinearMap.flip_apply, hcomm, Equiv.apply_symm_apply, ← hb, Equiv.symm_apply_apply]
    exact DFunLike.congr_fun hs x

end AlgebraicGeometry.Scheme.IdealSheafData
