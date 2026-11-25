/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Center
public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry
public import QPainleve.SignedClusterModularGroup.Realization.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Loops realizing signed Picard actions

A signed loop can realize a prescribed Picard action and intertwine fixed-center
X evaluations. For a marked presentation the witness includes the two centers
and the pair isomorphism whose X evaluation the loop realizes.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite
open QPainleve.CharacterTorus QPainleve.Cluster

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

open SignedBoundaryIsometryGroup (sign)

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "eval[" E "," w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))

/-- A loop realizing a prescribed signed Picard action and intertwining two
X evaluations at the generic point. For a positive action the loop has no inversions. -/
@[ext]
structure PicardLoopRealization {r n : ℕ} [NeZero n] {L : Type} [AddCommGroup L]
    {B : LinearMap.BilinForm ℤ L} {d : ZMod n → L} {E : SkewExchangeMatrix (Fin r)}
    {Z : Scheme} [IsIntegral Z]
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d)
    (g : signedBoundaryIsometryGroup B d) (source target : Z ⤏ XTor[r]) where
  /-- The chosen loop, in execution order. -/
  word : Word E E
  /-- The loop induces the prescribed signed Picard action. -/
  picard_eq : ρ eval[E,word] = g
  /-- For positive orientation the chosen loop uses no inversions. -/
  inversionCount_eq_zero : sign B d g = 1 → word.inversionCount = 0
  /-- Composing the source evaluation with the loop is defined at the generic
  point and gives the target evaluation. -/
  evaluation_eq : ∃ h, source.compOfDefined (word.xRationalMap ℂ) h = target

attribute [simp] PicardLoopRealization.picard_eq

variable {r n : ℕ} [NeZero n] {L N : Type} [AddCommGroup L] [AddCommGroup N]
  {B : LinearMap.BilinForm ℤ L} {d : ZMod n → L} {E : SkewExchangeMatrix (Fin r)}

/-- A loop realizing a prescribed signed Picard action on a marked center family.
The two centers and their pair isomorphism specify the evaluations intertwined
by the loop, and the source center lies in its noncollision open. -/
structure PresentationPicardLoopRealization (M : Point Centers[r] → MarkedSurface ℂ n B XTor[r])
    (P : ChargeSeed E N)
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d)
    (g : signedBoundaryIsometryGroup B d) where
  /-- The center of the source fiber. -/
  sourceCenter : Point Centers[r]
  /-- The center of the target fiber. -/
  targetCenter : Point Centers[r]
  /-- The isomorphism of pairs over the two centers. -/
  pairIso : (M sourceCenter).pair ≅ (M targetCenter).pair
  /-- The loop with the prescribed Picard action and fixed-center evaluation. -/
  loop :
    letI : IsIntegral (M sourceCenter).surface := (M sourceCenter).integral
    PicardLoopRealization ρ g (M sourceCenter).evaluation
      ((MarkedSurface.surfaceIso pairIso).hom.toRationalMap.comp (M targetCenter).evaluation)
  /-- The source center belongs to the loop's noncollision open. -/
  source_mem_centerOpen : sourceCenter.left (default : S) ∈ loop.word.centerOpen ℂ P

/-- The two centers, pair isomorphism, and loop word determine a presentation realization. -/
@[ext]
theorem PresentationPicardLoopRealization.ext
    {M : Point Centers[r] → MarkedSurface ℂ n B XTor[r]} {P : ChargeSeed E N}
    {ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup B d}
    {g : signedBoundaryIsometryGroup B d} {R R' : PresentationPicardLoopRealization M P ρ g}
    (hsource : R.sourceCenter = R'.sourceCenter) (htarget : R.targetCenter = R'.targetCenter)
    (hiso : HEq R.pairIso R'.pairIso) (hword : R.loop.word = R'.loop.word) : R = R' := by
  obtain ⟨c₀, c₁, e, w, _⟩ := R
  obtain ⟨c₀', c₁', e', w', _⟩ := R'
  dsimp only at hsource htarget hiso hword
  subst c₀' c₁'
  have he := eq_of_heq hiso
  subst e'
  cases PicardLoopRealization.ext hword
  rfl

end QPainleve.SignedClusterModularGroup.GeometricRealization
