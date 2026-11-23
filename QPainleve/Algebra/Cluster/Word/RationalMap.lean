/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Pullback
public import QPainleve.Geometry.Toric.CharacterTorus.RationalMap

/-!
# Rational X maps of cluster words

The pullback on the independent X function field defines the rational map of a word
on the X torus. Rational map composition is in execution order.
-/

public noncomputable section

open AlgebraicGeometry
open QPainleve.Cluster QPainleve.CharacterTorus

namespace Quiver.Path

universe u

variable {ι : Type u} [Finite ι] [DecidableEq ι] {B C D : SkewExchangeMatrix ι}
  (k : Type u) [Field k]

local notation "X" => scheme k (ι →₀ ℤ)
local notation "xRep" w:arg =>
  Equiv.symm (rationalPullbackEquiv k) (AlgEquiv.toAlgHom (xPullback k w))

/-- The rational transformation of the independent X torus given by a typed word. -/
def xRationalMap (w : Word B C) : X ⤏ X :=
  (xRep w).val

instance (w : Word B C) : (w.xRationalMap k).IsDominant :=
  (xRep w).property.left

instance (w : Word B C) :
    (w.xRationalMap k).IsOver (structureMap k (ι →₀ ℤ)) (structureMap k (ι →₀ ℤ)) :=
  (xRep w).property.right

/-- The scheme rational map pulls back by the independent X field equivalence. -/
@[simp]
theorem affineRationalPullback_xRationalMap (w : Word B C) :
    affineRationalPullback k (w.xRationalMap k) = (w.xPullback k).toRingHom :=
  affineRationalPullback_rationalPullbackEquiv_symm k _

@[simp]
theorem xRationalMap_nil :
    (Path.nil : Word B B).xRationalMap k = Scheme.RationalMap.id X := by
  apply (affineRationalPullback_eq_iff _ _).mp
  simp only [affineRationalPullback_xRationalMap, affineRationalPullback_id, xPullback_nil]
  rfl

/-- The rational X map of a concatenation performs the first word before the second. -/
@[simp]
theorem xRationalMap_comp (w : Word B C) (v : Word C D) :
    (w.comp v).xRationalMap k = (w.xRationalMap k).comp (v.xRationalMap k) := by
  apply (affineRationalPullback_eq_iff _ _).mp
  simp only [affineRationalPullback_xRationalMap, affineRationalPullback_comp, xPullback_comp]
  rfl

/-- Executing a word followed by its reversal induces the identity X map. -/
@[simp]
theorem xRationalMap_comp_reverse (w : Word B C) :
    (w.xRationalMap k).comp (w.reverse.xRationalMap k) = Scheme.RationalMap.id X := by
  simpa only [xRationalMap, xPullback_reverse, AlgEquiv.aut_inv] using
    rationalPullbackEquiv_symm_comp_symm k (w.xPullback k)

/-- Executing the reversal followed by the original word also induces the identity X map. -/
@[simp]
theorem xRationalMap_reverse_comp (w : Word B C) :
    (w.reverse.xRationalMap k).comp (w.xRationalMap k) = Scheme.RationalMap.id X := by
  simpa only [reverse_reverse] using xRationalMap_comp_reverse k w.reverse

end Quiver.Path
