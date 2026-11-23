/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.Regular.Scheme
import TauCeti.AlgebraicGeometry.Scheme.LocalDimension

/-!
# Local factoriality of smooth surfaces

The local rings of a smooth surface over a field are regular of dimension at most two,
hence are unique factorization domains.
-/

open AlgebraicGeometry CategoryTheory Order TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Every stalk of a scheme smooth of relative dimension two over a field is factorial. -/
public theorem uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 f] (x : X) :
    UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  have : Nonempty X := ⟨x⟩
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular X := IsRegular.of_smooth f
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)
  exact IsRegular.uniqueFactorizationMonoid_stalk x
    (WithBot.coe_le_coe.mp ((TauCeti.coheight_le_topologicalKrullDim x).trans hdim.le))

end AlgebraicGeometry.Scheme.Hom
