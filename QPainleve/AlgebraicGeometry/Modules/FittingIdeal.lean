/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.FittingIdeal.Pullback

import Mathlib.Algebra.Category.ModuleCat.Kernels
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Cokernels

/-!
# Zeroth Fitting ideals of cokernels

We compute the zeroth Fitting ideal of a cokernel on an affine spectrum and
transport it under pullback. These formulas use the affine equivalence
for quasi-coherent sheaves and Tau Ceti's Fitting ideal base change theorem.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

local notation "fit₀(" M ")" =>
  Scheme.Modules.fittingIdeal M
    (fun U ↦ Scheme.Modules.finite_sections_of_isAffineOpen _ U.val U.property) 0

variable {X : Scheme.{u}}

/-- The zeroth Fitting ideal of the cokernel of a map of associated sheaves on an
affine scheme is the ideal of the corresponding module cokernel. -/
theorem fittingIdeal_zero_cokernel_tilde {R : CommRingCat.{u}}
    {M N : ModuleCat.{u} R} [Module.Finite R N] (f : M ⟶ N) :
    fit₀(cokernel (tilde.map f)) =
      Scheme.IdealSheafData.ofIdealTop
        ((TauCeti.fittingIdeal R (N ⧸ LinearMap.range f.hom) 0).map
          (Scheme.ΓSpecIso R).inv.hom) := by
  let Q := ModuleCat.of R (N ⧸ LinearMap.range f.hom)
  let e := ModuleCat.cokernelIsoRangeQuotient f
  let e' : tilde Q ≅ cokernel (tilde.map f) :=
    (tilde.functor R).mapIso e.symm ≪≫ PreservesCokernel.iso (tilde.functor R) f
  have h := fittingIdeal_congr (M := tilde Q)
    (fun U ↦ finite_sections_of_isAffineOpen _ U.val U.property) e' 0
  rw [← h, fittingIdeal_Spec]
  have : Module.Finite R ((𝟭 (ModuleCat R)).obj Q) :=
    inferInstanceAs (Module.Finite R (N ⧸ LinearMap.range f.hom))
  have := Module.Finite.equiv (tilde.toTildeΓNatIso.app Q).toLinearEquiv
  exact congrArg (fun I : Ideal R ↦
    Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso R).inv.hom))
    (TauCeti.fittingIdeal_congr (tilde.toTildeΓNatIso.app Q).toLinearEquiv.symm 0)

/-- The zeroth Fitting ideal of the cokernel of a map of quasi-coherent modules
commutes with pullback. -/
theorem fittingIdeal_zero_cokernel_comap {Y : Scheme.{u}} (p : Y ⟶ X)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType]
    (f : M ⟶ N) :
    fit₀(cokernel ((pullback p).map f)) = (fit₀(cokernel f)).comap p :=
  (fittingIdeal_congr (fun U ↦ finite_sections_of_isAffineOpen _ U.val U.property)
    (PreservesCokernel.iso (pullback p) f).symm 0).trans (fittingIdeal_pullback p _ 0)

/-- On an affine scheme, the zeroth Fitting ideal sheaf of the cokernel of a
quasi-coherent module map is computed by taking the cokernel on global sections. -/
theorem fittingIdeal_zero_cokernel_Spec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType]
    (f : M ⟶ N) :
    letI := N.finite_moduleSpecΓ
    fit₀(cokernel f) = Scheme.IdealSheafData.ofIdealTop
      ((TauCeti.fittingIdeal R
        ((moduleSpecΓFunctor.obj N) ⧸ LinearMap.range (moduleSpecΓFunctor.map f).hom) 0).map
          (Scheme.ΓSpecIso R).inv.hom) := by
  have := N.finite_moduleSpecΓ
  let ε := (tilde.adjunction (R := R)).counit
  have : IsIso (ε.app M) := isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso (ε.app N) := isIso_fromTildeΓ_of_isQuasicoherent N
  let e := cokernel.mapIso _ f (asIso (ε.app M)) (asIso (ε.app N)) (ε.naturality f)
  exact (fittingIdeal_congr _ e.symm 0).trans (fittingIdeal_zero_cokernel_tilde _)

/-- The zeroth Fitting ideal of a zero sheaf of modules is the unit ideal. -/
theorem fittingIdeal_zero_eq_top_of_isZero (M : X.Modules) [M.IsQuasicoherent]
    [M.IsFiniteType] (hM : IsZero M) : fit₀(M) = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  have : Subsingleton Γ(M, U.val) :=
    ModuleCat.isZero_iff_subsingleton.mp (Functor.map_isZero (sectionsFunctor U.val) hM)
  rw [fittingIdeal_ideal, (TauCeti.fittingIdeal_zero_eq_top_iff).mpr inferInstance]
  rfl

end AlgebraicGeometry.Scheme.Modules
