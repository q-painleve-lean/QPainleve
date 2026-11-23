/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Kernel
public import QPainleve.Geometry.Toric.CharacterTorus.CenterAlignment

/-!
# The translation stabilizer of a charge map

The kernel of the map of character tori induced by a charge homomorphism
represents the translations that preserve the center coordinates. Its rational
points act on the choices of an aligning translation. Choosing a reference
translation identifies the full fiber with the points of the kernel, with the
ratio to the reference giving the kernel point.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Multiplicative
open TauCeti TauCeti.DiagonalizableGroup
open scoped CategoryTheory.MonObj

namespace QPainleve.CharacterTorus

universe u

variable (k : Type u) [CommRing k]
variable {A N : Type u} [AddCommGroup A] [AddCommGroup N] [IsAddFG A] [IsAddFG N]

local notation "T" => Scheme.asOver (Spec (CommRingCat.of k)) (Spec (CommRingCat.of k))
local notation "L" B => FGCommGrpCat.of (Multiplicative B)
local notation "chargeMap" v =>
  groupSchemeMap k (FGCommGrpCat.ofHom (AddMonoidHom.toMultiplicative v))

/-- Points of the kernel of the charge morphism are exactly the translations fixing the
center coordinates. -/
def translationKernelPointsMulEquiv (v : A →+ N) :
    (T ⟶ (kernel (chargeMap v)).X) ≃* (v.toMultiplicative.compHom' (P := kˣ)).ker :=
  (kernelSchemePointsMulEquiv k (FGCommGrpCat.ofHom v.toMultiplicative) k).trans
    ((MonoidHom.domRestrictHomKerEquiv kˣ v.range.toSubgroup).symm.trans
      (MulEquiv.subgroupCongr (translationKernel_eq k v).symm))

/-- The stabilizing character is the ambient torus point obtained by the kernel inclusion. -/
@[simp]
theorem coe_translationKernelPointsMulEquiv_apply (v : A →+ N)
    (z : T ⟶ (kernel (chargeMap v)).X) :
    (translationKernelPointsMulEquiv k v z : Multiplicative N →* kˣ) =
      schemePointsMulEquiv (R := k) (A := k) (L N) (z ≫ (kernel.ι (chargeMap v)).hom.hom) := by
  rw [schemePointsMulEquiv_comp_kernel_ι]
  rfl

/-- A reference translation identifies its charge fiber with the points of the
scheme-theoretic kernel. -/
def translationFiberKernelPointsEquiv (v : A →+ N) (z₀ : Multiplicative N →* kˣ) :
    {z : Multiplicative N →* kˣ // z.comp v.toMultiplicative = z₀.comp v.toMultiplicative} ≃
      (T ⟶ (kernel (chargeMap v)).X) :=
  (v.toMultiplicative.compHom' (P := kˣ)).fiberEquivKer z₀ |>.trans
    (translationKernelPointsMulEquiv k v).symm.toEquiv

/-- The point attached to a translation is its ratio to the reference translation,
viewed by the kernel inclusion as a character of the ambient lattice. -/
@[simp]
theorem schemePointsMulEquiv_comp_translationFiberKernelPointsEquiv
    (v : A →+ N) (z₀ : Multiplicative N →* kˣ)
    (z : {z : Multiplicative N →* kˣ // z.comp v.toMultiplicative = z₀.comp v.toMultiplicative}) :
    schemePointsMulEquiv (R := k) (A := k) (L N)
      (translationFiberKernelPointsEquiv k v z₀ z ≫ (kernel.ι (chargeMap v)).hom.hom) =
        z₀⁻¹ * z.val := by
  rw [← coe_translationKernelPointsMulEquiv_apply]
  exact congrArg Subtype.val ((translationKernelPointsMulEquiv k v).apply_symm_apply
    ((v.toMultiplicative.compHom' (P := kˣ)).fiberEquivKer z₀ z))

/-- Multiplying the reference translation by a kernel point gives the corresponding
translation in its fiber. -/
@[simp]
theorem coe_translationFiberKernelPointsEquiv_symm_apply
    (v : A →+ N) (z₀ : Multiplicative N →* kˣ) (z : T ⟶ (kernel (chargeMap v)).X) :
    ((translationFiberKernelPointsEquiv k v z₀).symm z).val =
      z₀ * schemePointsMulEquiv (R := k) (A := k) (L N)
        (z ≫ (kernel.ι (chargeMap v)).hom.hom) := by
  have h := schemePointsMulEquiv_comp_translationFiberKernelPointsEquiv k v z₀
    ((translationFiberKernelPointsEquiv k v z₀).symm z)
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  exact (mul_inv_cancel_left z₀ _).symm

end QPainleve.CharacterTorus
