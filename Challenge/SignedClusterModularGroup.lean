/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
import Challenge.SignedClusterModularGroup.Definitions

/-!
# Challenge: the signed cluster modular group of a toric presentation

The target-pair conditions on the total boundary class are primitivity, nefness, and square zero.
-/

noncomputable section

namespace QPainleveChallenge.Toric

open TauCeti Matrix

/-! ## The challenge -/

/-- **Challenge.** -/
theorem nonempty_mulEquiv_signedBoundaryIsometryGroup
    {r : ℕ} [NeZero r] (u : ZMod r → ℤ × ℤ) (hu : IsSmoothCompleteFan u)
    {I : Type} [Fintype I] [DecidableEq I] (ρ : I → ZMod r) (c : List (ZMod r))
    (hc : IsContraction u ρ c) (_hY : IsTargetPair u ρ c) :
    Nonempty (SignedClusterModularGroup (exchangeMatrix u ρ) ≃*
      signedBoundaryIsometryGroup (picForm u ρ hu c) (boundary u ρ hu hc)) := by
  sorry

/-! ## The challenge for the two presentations -/

/-- The challenge for the four-vertex seed. -/
theorem FourVertex.nonempty_mulEquiv :
    Nonempty (SignedClusterModularGroup (exchangeMatrix FourVertex.rays FourVertex.center) ≃*
      signedBoundaryIsometryGroup (picForm FourVertex.rays FourVertex.center
        FourVertex.isSmoothCompleteFan [])
        (boundary FourVertex.rays FourVertex.center FourVertex.isSmoothCompleteFan
          FourVertex.isContraction)) :=
  nonempty_mulEquiv_signedBoundaryIsometryGroup _ _ _ _ _ FourVertex.isTargetPair

/-- The challenge for the one-component example. -/
theorem OneComponent.nonempty_mulEquiv :
    Nonempty (SignedClusterModularGroup (exchangeMatrix OneComponent.rays OneComponent.center) ≃*
      signedBoundaryIsometryGroup (picForm OneComponent.rays OneComponent.center
        OneComponent.isSmoothCompleteFan OneComponent.contraction)
        (boundary OneComponent.rays OneComponent.center OneComponent.isSmoothCompleteFan
          OneComponent.isContraction)) :=
  nonempty_mulEquiv_signedBoundaryIsometryGroup _ _ _ _ _ OneComponent.isTargetPair

end QPainleveChallenge.Toric

end
