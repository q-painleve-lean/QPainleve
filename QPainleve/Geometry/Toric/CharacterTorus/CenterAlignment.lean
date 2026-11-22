/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.FieldTheory.IsAlgClosed.Units
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Center alignment for character tori

For a charge map `v : A →+ N`, translation acts on a center character by multiplying it by
the pullback of a character of `N`. Over an algebraically closed field its orbits are the
fibers of restriction to the charge kernel. The translation stabilizer is the character
group of the quotient by the charge image, with free unit coordinates and root-of-unity
coordinates in a Smith basis, as described in
`QPainleve.LinearAlgebra.SmithQuotientCharacters`.

The extension of characters uses Mathlib's Baer criterion and Tau Ceti's divisibility of
units of algebraically closed fields.
-/

public noncomputable section

open Multiplicative

namespace QPainleve.CharacterTorus

variable (k : Type*) {A N : Type*} [CommMonoid k] [AddCommGroup A] [AddCommGroup N]

/-- A translation character acts trivially on the center coordinates precisely when it
comes from the quotient by the charge image. -/
def translationKernelEquiv (v : A →+ N) :
    (v.toMultiplicative.compHom' (P := kˣ)).ker ≃* (Multiplicative (N ⧸ v.range) →* kˣ) :=
  (MulEquiv.subgroupCongr (by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.domRestrictHom_apply,
      MonoidHom.domRestrict_eq_one_iff]
    exact (MonoidHom.range_le_ker_iff v.toMultiplicative z).symm)).trans
    (MonoidHom.domRestrictHomKerEquiv kˣ v.range.toSubgroup)

@[simp]
theorem translationKernelEquiv_apply (v : A →+ N)
    (z : (v.toMultiplicative.compHom' (P := kˣ)).ker) (x : N) :
    translationKernelEquiv k v z (ofAdd (x : N ⧸ v.range)) =
      z.val (ofAdd x) := (rfl)

@[simp]
theorem translationKernelEquiv_symm_apply (v : A →+ N)
    (j : Multiplicative (N ⧸ v.range) →* kˣ) (x : N) :
    ((translationKernelEquiv k v).symm j).val (ofAdd x) =
      j (ofAdd (x : N ⧸ v.range)) := (rfl)

/-- With a reference translation `z₀`, all translations having the same action on the centers
form a torsor for the characters of the charge quotient. -/
def translationFiberEquiv (v : A →+ N) (z₀ : Multiplicative N →* kˣ) :
    {z : Multiplicative N →* kˣ // z.comp v.toMultiplicative = z₀.comp v.toMultiplicative} ≃
      (Multiplicative (N ⧸ v.range) →* kˣ) :=
  ((v.toMultiplicative.compHom' (P := kˣ)).fiberEquivKer z₀).trans
    (translationKernelEquiv k v).toEquiv

@[simp]
theorem translationFiberEquiv_apply (v : A →+ N) (z₀ : Multiplicative N →* kˣ)
    (z : {z : Multiplicative N →* kˣ // z.comp v.toMultiplicative = z₀.comp v.toMultiplicative})
    (x : N) :
    translationFiberEquiv k v z₀ z (ofAdd (x : N ⧸ v.range)) =
      (z₀ (ofAdd x))⁻¹ * z.val (ofAdd x) := (rfl)

@[simp]
theorem translationFiberEquiv_symm_apply (v : A →+ N) (z₀ : Multiplicative N →* kˣ)
    (j : Multiplicative (N ⧸ v.range) →* kˣ) (x : N) :
    ((translationFiberEquiv k v z₀).symm j).val (ofAdd x) =
      z₀ (ofAdd x) * j (ofAdd (x : N ⧸ v.range)) := (rfl)

variable {k}

/-- Two centers are related by a translation exactly when their characters agree on the
charge kernel. The existence direction extends their ratio from the charge image to the
ambient group and applies in every rank. -/
theorem exists_center_translation_iff [RootableBy kˣ ℕ]
    (v : A →+ N) (c₁ c₂ : Multiplicative A →* kˣ) :
    (∃ z : Multiplicative N →* kˣ, c₁ * z.comp v.toMultiplicative = c₂) ↔
      ∀ a ∈ v.ker, c₁ (ofAdd a) = c₂ (ofAdd a) := by
  constructor
  · rintro ⟨z, rfl⟩ a ha
    simp [AddMonoidHom.mem_ker.mp ha]
  · intro h
    let d := (c₂ / c₁).toAdditiveRight
    let q := QuotientAddGroup.lift v.ker d fun a ha ↦ by
      simp [d, h a ha]
    let e := QuotientAddGroup.quotientKerEquivRange v
    let dH := q.comp e.symm.toAddMonoidHom
    let : DivisibleBy (Additive kˣ) ℕ :=
      ⟨RootableBy.root (A := kˣ), RootableBy.root_zero (A := kˣ),
        fun a hn ↦ RootableBy.root_cancel (A := kˣ) a hn⟩
    let : DivisibleBy (Additive kˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
    obtain ⟨u, hu⟩ := (Module.Baer.of_divisible (Additive kˣ)).extension_property_addMonoidHom
      v.range.subtype Subtype.val_injective dH
    refine ⟨MonoidHom.toAdditiveRight.symm u, ?_⟩
    have hq (a : A) : dH (v.rangeRestrict a) = d a := by
      have he : e (QuotientAddGroup.mk' v.ker a) = v.rangeRestrict a := rfl
      rw [← he, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
      rfl
    apply MonoidHom.ext
    intro a
    have hu' : MonoidHom.toAdditiveRight.symm u (v.toMultiplicative a) = c₂ a / c₁ a :=
      congrArg Additive.toMul ((DFunLike.congr_fun hu (v.rangeRestrict a)).trans (hq a))
    exact mul_eq_of_eq_div' hu'

end QPainleve.CharacterTorus
