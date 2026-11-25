/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# Conjugation by a bilinear isometry

An isometry between two given bilinear forms identifies their isometry groups.
This is the restriction of linear conjugation given by
`LinearMap.BilinForm.isometryGroupCongr`.
-/

public section

namespace LinearMap.BilinForm.IsometryEquiv

open LinearMap (BilinForm)

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] {B : BilinForm R M} {C : BilinForm R N}

/-- An isometry conjugates the automorphisms of its source form to those of its
target form. -/
def isometryGroupCongr (e : B.IsometryEquiv C) : B.isometryGroup ≃* C.isometryGroup :=
  (B.isometryGroupCongr e.toLinearEquiv).trans (MulEquiv.cast
    (M := fun D : BilinForm R N ↦ ↥D.isometryGroup) (by
      ext x y
      exact e.symm.map_app y x))

@[simp]
theorem isometryGroupCongr_apply_apply (e : B.IsometryEquiv C) (g : B.isometryGroup) (x : N) :
    (e.isometryGroupCongr g).val x = e (g.val (e.symm x)) := by
  have coe_cast {D E : BilinForm R N} (h : D = E) (a : D.isometryGroup) :
      (MulEquiv.cast (M := fun F : BilinForm R N ↦ ↥F.isometryGroup) h a).val = a.val := by
    subst E
    rfl
  rw [isometryGroupCongr, MulEquiv.trans_apply, coe_cast,
    LinearMap.BilinForm.coe_isometryGroupCongr_apply]
  rfl

end LinearMap.BilinForm.IsometryEquiv
