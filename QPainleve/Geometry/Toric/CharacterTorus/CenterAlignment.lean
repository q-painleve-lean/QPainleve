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
Mathlib's `MonoidHom.domRestrictHomKerEquiv` identifies the stabilizer with these
quotient characters.

The ratio of two center characters agreeing on the charge kernel descends to the charge image
by `AddMonoidHom.liftOfSurjective`. Mathlib's Baer criterion extends it to the ambient group,
using Tau Ceti's divisibility of units for algebraically closed fields.
-/

public noncomputable section

open Multiplicative

namespace QPainleve.CharacterTorus

variable (k : Type*) {A N : Type*} [CommMonoid k] [AddCommGroup A] [AddCommGroup N]

/-- The translations fixing the center coordinates are the characters trivial on the
charge image. -/
theorem translationKernel_eq (v : A →+ N) :
    (v.toMultiplicative.compHom' (P := kˣ)).ker =
      (MonoidHom.domRestrictHom v.range.toSubgroup kˣ).ker := by
  ext z
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.domRestrictHom_apply,
    MonoidHom.domRestrict_eq_one_iff]
  exact (MonoidHom.range_le_ker_iff v.toMultiplicative z).symm

/-- With a reference translation `z₀`, all translations having the same action on the centers
form a torsor for the characters of the charge quotient. -/
def translationFiberEquiv (v : A →+ N) (z₀ : Multiplicative N →* kˣ) :
    {z : Multiplicative N →* kˣ // z.comp v.toMultiplicative = z₀.comp v.toMultiplicative} ≃
      (Multiplicative (N ⧸ v.range) →* kˣ) :=
  ((v.toMultiplicative.compHom' (P := kˣ)).fiberEquivKer z₀).trans
    ((MulEquiv.subgroupCongr (translationKernel_eq k v)).toEquiv.trans
      (MonoidHom.domRestrictHomKerEquiv kˣ v.range.toSubgroup).toEquiv)

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

/-- Two centers are related by a translation exactly when their characters agree on the
charge kernel. The existence direction extends their ratio from the charge image to the
ambient group for any rootable commutative group of character values. -/
theorem exists_center_translation_iff {G : Type*} [CommGroup G] [RootableBy G ℕ]
    (v : A →+ N) (c₁ c₂ : Multiplicative A →* G) :
    (∃ z : Multiplicative N →* G, c₁ * z.comp v.toMultiplicative = c₂) ↔
      ∀ a ∈ v.ker, c₁ (ofAdd a) = c₂ (ofAdd a) := by
  constructor
  · rintro ⟨z, rfl⟩ a ha
    simp [AddMonoidHom.mem_ker.mp ha]
  · intro h
    let ratio := (c₂ / c₁).toAdditiveRight
    have hker : v.rangeRestrict.ker ≤ ratio.ker := by
      rw [AddMonoidHom.ker_rangeRestrict]
      intro a ha
      simp [ratio, h a ha]
    let : DivisibleBy (Additive G) ℕ :=
      ⟨RootableBy.root (A := G), RootableBy.root_zero (A := G),
        fun a hn ↦ RootableBy.root_cancel (A := G) a hn⟩
    let : DivisibleBy (Additive G) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
    obtain ⟨u, hu⟩ := (Module.Baer.of_divisible (Additive G)).extension_property_addMonoidHom
      v.range.subtype Subtype.val_injective
      (v.rangeRestrict.liftOfSurjective v.rangeRestrict_surjective ⟨ratio, hker⟩)
    refine ⟨MonoidHom.toAdditiveRight.symm u, ?_⟩
    apply MonoidHom.ext
    intro a
    apply mul_eq_of_eq_div'
    simpa [ratio] using congrArg Additive.toMul (DFunLike.congr_fun hu (v.rangeRestrict a.toAdd))

end QPainleve.CharacterTorus
