/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Boundary.Isometry
public import QPainleve.SignedClusterModularGroup.Realization.Surface

/-!
# Pair isomorphisms with a prescribed signed Picard action

A marked pair isomorphism realizes a signed boundary isometry when its Picard pullback
and its orientation on ordered branches agree with the prescribed action. The forward
permutation of the numbered components comes from the pair isomorphism.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace QPainleve.SignedClusterModularGroup

open MarkedSurface (boundaryIso surfaceIso)
open SignedBoundaryIsometryGroup (sign toIsometry)

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L : Type u} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L} {d : ZMod n → L}
  {X Y : Scheme.{u}}

local notation "S" => Spec (CommRingCat.of k)

/-- An isomorphism of marked pairs inducing a specified Picard pullback and branch sign.
The ordered-branch action distinguishes both signs even for one or two components. -/
@[ext]
structure SignedPicardPairIso (M : MarkedSurface k n B X) (N : MarkedSurface k n B Y)
    (g : signedBoundaryIsometryGroup B d) where
  /-- The isomorphism of surface pairs over the ground field. -/
  iso : M.pair ≅ N.pair
  /-- The geometric branch sign equals the specified sign. -/
  sign_eq :
    letI : PrestableFamily (M.boundary ↘ S) := M.prestable
    letI : PrestableFamily (N.boundary ↘ S) := N.prestable
    cycleOrientationSign ((boundaryIso iso).boundaryCycleAction M.cycle N.cycle) = sign B d g
  /-- The pullback in the fixed markings is the specified isometry. -/
  picard_eq (a : L) :
    M.picardMarking ((toIsometry B d g).val a) =
      Additive.ofMul (LineBundleClass.pullback (surfaceIso iso).hom (N.picardMarking a).toMul)

attribute [simp] SignedPicardPairIso.sign_eq

end QPainleve.SignedClusterModularGroup
