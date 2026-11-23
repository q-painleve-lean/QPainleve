/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.Coalgebra.GroupLike

import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints

/-!
# Translation on spectra with group-like coordinates

A coordinate map that scales each group-like basis element by its value at a point
induces left translation by that point on the relative spectrum.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory WithConv
open scoped MonObj

namespace QPainleve

universe u

variable {k H : Type u} [CommRing k] [CommRing H] [Bialgebra k H]

local notation "S" => Spec (CommRingCat.of k)
local notation "X" => (OverClass.asOver (Spec (CommRingCat.of H)) S)

/-- Scaling a group-like basis by its values at a point induces left multiplication by
that point on the relative spectrum. -/
theorem specMap_eq_mul_of_groupLike_basis {I : Type*} (b : Module.Basis I k H)
    (hb : ∀ i, IsGroupLikeElem k (b i)) (p : H →ₐ[k] k) (f : H →ₐ[k] H)
    (hf : ∀ i, f (b i) = p (b i) • b i) (x : 𝟙_ (Over S) ⟶ X)
    (hx : x.left = Spec.map (CommRingCat.ofHom p.toRingHom)) :
    ((Spec.map (CommRingCat.ofHom f.toRingHom)).asOver S : X ⟶ X) =
      (toUnit X ≫ x) * 𝟙 X := by
  have hconst : Spec.mapMulEquiv (toConv ((Algebra.ofId k H).comp p)) =
      toUnit X ≫ x := by
    apply Over.OverMorphism.ext
    rw [TauCeti.CommHopfAlgCat.mapMulEquiv_left, Over.comp_left, Over.toUnit_left, hx]
    change _ = Spec.map (CommRingCat.ofHom (algebraMap k H)) ≫
      Spec.map (CommRingCat.ofHom p.toRingHom)
    rw [← Spec.map_comp]
    rfl
  have hid : Spec.mapMulEquiv (toConv (AlgHom.id k H)) = 𝟙 X :=
    Over.OverMorphism.ext <|
      (TauCeti.CommHopfAlgCat.mapMulEquiv_left _).trans (Spec.map_id _)
  have hconv : toConv f = toConv ((Algebra.ofId k H).comp p) * toConv (AlgHom.id k H) := by
    apply WithConv.ofConv_injective
    apply AlgHom.toLinearMap_injective
    apply b.ext
    intro i
    change f (b i) = (toConv ((Algebra.ofId k H).comp p) * toConv (AlgHom.id k H)) (b i)
    rw [hf, AlgHom.convMul_apply, (hb i).comul_eq_tmul_self]
    simp [Algebra.smul_def]
  rw [← hconst, ← hid, ← map_mul, ← hconv]
  apply Over.OverMorphism.ext
  exact (OverClass.asOverHom_left _ _).trans
    (TauCeti.CommHopfAlgCat.mapMulEquiv_left (toConv f)).symm

end QPainleve
