/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.SelfRealization

/-!
# The signed Picard action of a marked toric presentation

The laws of a signed Picard action describe its evaluation on a realized loop,
its sign on any loop, and the image of the unsigned group on point maps. The
homomorphism and the equivalence use the same laws.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite
open Module (Basis)
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "eval[" E "," w "]" => op (signedClusterModularGroupMap ℂ E (End.of w))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {E : SkewExchangeMatrix (Fin r)}

variable (Q : CompleteToricPresentation i b r L γ)

/-- A signed Picard action agrees with marked geometric pullback on compatible
realizations, has the inversion sign of each representative, and has the unsigned
group as its sign kernel on point maps. -/
structure IsSignedPicardAction
    (M : Point Centers[r] → MarkedSurface ℂ n H XTor[r])
    {d : ZMod n → L} (hD : ∀ c, D[M c].IsEffectiveCartier)
    (hmark : ∀ c j, (M c).boundaryClass (hD c) j = d j)
    (ρ : (SignedClusterModularGroup ℂ E)ᵐᵒᵖ →* signedBoundaryIsometryGroup H d) : Prop where
  /-- The sign of the Picard action is the inversion parity of the representing word. -/
  sign_apply_word (w : Word E E) :
    sign H d (ρ eval[E,w]) = (-1 : ℤˣ) ^ w.inversionCount
  /-- The action on a word is the marked pullback and branch sign of any realization
  whose target fibers have models in the presentation. -/
  apply_of_realization (w : Word E E)
      {C : Centers[r].left.PartialMap Centers[r].left} [IsDominant C.hom]
      [C.IsOver Centers[r].hom Centers[r].hom]
      (R : GeometricRealization M M C (w.xRationalMap ℂ))
      (hC :
        letI := Q.complete.nonempty_cones
        letI := Q.prestable
        letI := Q.neZero
        HasToricTargetModels (T₀ := Centers[r]) (T₁ := Centers[r]) (b := b) (s := Q.rays)
          (hΦ := Q.regular) (T := Q.cycle) (origin := Q.origin) (ι := Q.inclusion) (P₁ := M)
          (fun z : Point Centers[r] ↦ χ[z]) C) :
    ρ eval[E,w] = R.toSignedBoundaryIsometry d hD hmark
  /-- On point maps, the sign kernel is the image of the unsigned group. -/
  sign_ker_unop : ((sign H d).comp ρ).ker.unop = (clusterModularGroupInclusion ℂ E).range

end QPainleve.SignedClusterModularGroup.GeometricRealization
