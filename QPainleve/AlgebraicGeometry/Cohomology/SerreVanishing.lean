/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Cohomology.ProjectiveSpace.SerreVanishing
public import QPainleve.AlgebraicGeometry.LineBundle.Ample

/-!
# Serre vanishing for ample twists

On a proper scheme over a Noetherian ring, sufficiently high powers of an ample line
bundle kill positive cohomology of a coherent sheaf, with one bound for every degree.
This is the vanishing statement of the Stacks Project,
[Lemma 30.16.1(4)](https://stacks.math.columbia.edu/tag/0B5T). The proof applies the finite
projective comparison to a positive power of the ample bundle.
-/

public section

open AlgebraicGeometry Filter CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Serre vanishing.** On a proper scheme over a Noetherian ring, every sufficiently high
ample twist of a quasi-coherent sheaf of finite type has vanishing cohomology in all positive
degrees. -/
theorem eventually_subsingleton_cohomology_tensorPow_of_isAmple
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (L : InvertibleSheaf X) (hL : (LineBundleClass.mk L).IsAmple) :
    ∀ᶠ m : ℕ in atTop, ∀ q : ℕ, 0 < q →
      Subsingleton (Cohomology (F ⊗ (L.tensorPow m).obj) q) := by
  obtain ⟨d, hd, ι, _, g, _, _, e⟩ := hL.exists_finite_to_proj_tensorPow f
  exact g.eventually_subsingleton_cohomology_tensorPow_of_finite_to_proj
    (Finsupp.basisSingleOne (R := R) (ι := ι)) F L hd e

end AlgebraicGeometry.Scheme.Hom
