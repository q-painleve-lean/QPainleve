/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Excision

/-!
# Effective Picard classes

Effective Cartier divisors determine an additive submonoid of the Picard group.
On a Noetherian locally factorial scheme this is also the image of nonnegative Weil divisors.
-/

public noncomputable section

open AlgebraicGeometry
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.CartierDivisor

universe u

local notation "Pic(" Z ")" => Additive (LineBundleClass Z)
local notation "cl" => weilToLineBundleClassHom
local notation "P" => LineBundleClass.primeDivisorClass

namespace AlgebraicGeometry.Scheme

/-- The additive submonoid of Picard classes represented by effective Cartier divisors. -/
def effectiveClasses (X : Scheme.{u}) [IsIntegral X] : AddSubmonoid Pic(X) :=
  (effectiveSubmonoid X).map toLineBundleClassHom

variable {X : Scheme.{u}} [IsIntegral X]

/-- An effective Picard class is represented by an effective Cartier divisor. -/
theorem mem_effectiveClasses {a : Pic(X)} :
    a ∈ X.effectiveClasses ↔
      ∃ D : TauCeti.AlgebraicGeometry.Scheme.CartierDivisor X,
        D.IsEffective ∧ Additive.ofMul D.toLineBundleClass = a := by
  simp only [effectiveClasses, AddSubmonoid.mem_map, mem_effectiveSubmonoid,
    toLineBundleClassHom_apply]

/-- If the difference of two classes is effective, ineffectivity of a twist of the first
class implies ineffectivity of the same twist of the second. -/
theorem notMem_effectiveClasses_add_of_sub_mem {a b c : Pic(X)}
    (ha : c + a ∉ X.effectiveClasses) (hab : a - b ∈ X.effectiveClasses) :
    c + b ∉ X.effectiveClasses := fun h ↦ ha (by
  have hsum := X.effectiveClasses.add_mem hab h
  rwa [show a - b + (c + b) = c + a by abel] at hsum)

variable [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- On a Noetherian locally factorial scheme, a Picard class is effective exactly when
it is represented by a nonnegative Weil divisor. -/
theorem mem_effectiveClasses_iff_exists_weilDivisor {a : Pic(X)} :
    a ∈ X.effectiveClasses ↔ ∃ D : SchemeWeilDivisor X, 0 ≤ D ∧ cl X D = a := by
  have : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  have h := (toWeilDivisorAddEquiv X).surjective.exists (p := fun D ↦ 0 ≤ D ∧ cl X D = a)
  simpa only [mem_effectiveClasses, toWeilDivisorAddEquiv_apply,
    ← isEffective_iff_toWeilDivisor_nonneg, weilToLineBundleClassHom_toWeilDivisor] using h.symm

/-- The Picard class of a prime divisor is effective. -/
@[simp]
theorem primeDivisorClass_mem_effectiveClasses (p : CodimensionOnePoint X) :
    Additive.ofMul (P p) ∈ X.effectiveClasses := by
  refine mem_effectiveClasses_iff_exists_weilDivisor.mpr ⟨Finsupp.single p 1, by simp, ?_⟩
  simp only [weilToLineBundleClassHom_single, one_smul, ← LineBundleClass.primeDivisorClass_def]

end AlgebraicGeometry.Scheme
