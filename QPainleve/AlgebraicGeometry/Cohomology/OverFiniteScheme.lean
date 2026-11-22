/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.EulerCharacteristic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import TauCeti.AlgebraicGeometry.Cohomology.Affine
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic

/-!
# Cohomology over a finite scheme

Zeroth cohomology of a finite type quasi-coherent sheaf on a scheme finite over an affine
base is finite over the base ring. For a short exact sequence with quotient carried by
a closed subscheme finite over a field, this supplies the finiteness and vanishing needed
to apply Euler characteristic additivity in degrees zero and one.
-/

public section

open CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite type quasi-coherent sheaf on a scheme finite over an affine base has
module-finite zeroth cohomology over the base ring. -/
theorem moduleFinite_cohomology_zero_of_isFinite (R : Type u) [CommRing R]
    {Z : Scheme.{u}} [Z.Over (Spec (.of R))] [IsFinite (Z ↘ Spec (.of R))]
    (M : Z.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    Module.Finite R (Cohomology M 0) := by
  let p := Z ↘ Spec (.of R)
  have : IsAffine Z := isAffine_of_isAffineHom p
  let : Algebra R Γ(Z, ⊤) := (baseRingToGlobalSections R Z).toAlgebra
  have : Module.Finite R Γ(Z, ⊤) :=
    p.moduleFinite_appTop (RingHom.ext (baseRingToGlobalSections_apply R Z))
  have : Module.Finite Γ(Z, ⊤) Γ(M, ⊤) :=
    M.finite_sections_of_isAffineOpen _ (isAffineOpen_top Z)
  have : IsScalarTower R Γ(Z, ⊤) Γ(M, ⊤) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have : Module.Finite R Γ(M, ⊤) := Module.Finite.trans Γ(Z, ⊤) _
  exact Module.Finite.equiv (cohomologyZeroBaseLinearEquiv R Z M).symm

/-- In a short exact sequence on a scheme over a field, suppose the quotient is the direct
image of a finite type quasi-coherent sheaf on a finite closed subscheme. If the middle term
has finite-dimensional cohomology in degrees zero and one and vanishes in degree two, then
the Euler characteristics truncated at degree two are additive. -/
theorem eulerCharBelow_eq_add_of_finite_quotient (k : Type u) [Field k]
    {Y Z : Scheme.{u}} [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsFinite (Z ↘ Spec (.of k))] (i : Z ⟶ Y) [i.IsOver (Spec (.of k))]
    [IsClosedImmersion i] {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    (G : Z.Modules) [G.IsQuasicoherent] [G.IsFiniteType]
    (e : S.X₃ ≅ (Scheme.Modules.pushforward i).obj G)
    (hfin : ∀ n < 2, FiniteDimensional k (Cohomology S.X₂ n))
    (hvan : Subsingleton (Cohomology S.X₂ 2)) :
    eulerCharBelow k Y S.X₂ 2 = eulerCharBelow k Y S.X₁ 2 + eulerCharBelow k Y S.X₃ 2 := by
  let comparison (n : ℕ) := (cohomologyBaseLinearEquivOfIso k e n).trans
    (i.cohomologyPushforwardBaseLinearEquiv k G n)
  have : FiniteDimensional k (Cohomology S.X₃ 0) :=
    have := moduleFinite_cohomology_zero_of_isFinite k G
    Module.Finite.equiv (comparison 0).symm
  have : FiniteDimensional k (Cohomology S.X₂ 1) := hfin 1 (by decide)
  have h₁ := finiteDimensional_cohomology_X₁ k Y hS 0 1 rfl
  have : Subsingleton (Cohomology G 1) :=
    subsingleton_cohomology_succ_of_isAffineHom (Z ↘ Spec (.of k)) G 0
  exact eulerCharBelow_eq_add k hS 2
    (fun n hn hp ↦ by
      obtain rfl : n = 1 := by omega
      exact h₁) hfin
    (subsingleton_cohomology_X₁ hS 1 2 rfl (comparison 1).toEquiv.subsingleton hvan)

end AlgebraicGeometry.Scheme.Modules
