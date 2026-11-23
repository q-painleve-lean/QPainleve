/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Instances
import TauCeti.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.HigherCohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.Vanishing
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian
import TauCeti.AlgebraicGeometry.Modules.FiniteType
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.LinearAction
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalGeneration

/-!
# Finiteness of coherent cohomology on projective schemes

Over a Noetherian ring, the cohomology of a quasi-coherent sheaf of finite type on a
projective scheme is finitely generated in every degree. On projective space, descending
induction uses the long exact cohomology sequence of a quotient of a finite sum of
twisting sheaves. A closed immersion into projective space then gives the result for
projective schemes by the base-linear direct image comparison.

The proof follows the Stacks Project, Lemmas 30.14.1 (tag 01YS) and 30.16.1 (tag 0B5T).
It uses Tau Ceti's `Proj.eventually_exists_epi_free_tensor_twistingSheaf`,
`Module.Basis.finite_cohomology_twistingSheaf`, and
`Scheme.Hom.moduleFinite_cohomology_pushforward_iff`.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open TauCeti.AlgebraicGeometry.Scheme.Modules
open TauCeti.SymmetricAlgebra

universe u

namespace Module.Basis

open Scheme.Modules

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]

local notation "𝒜" => homogeneousSubmodule R M
local notation "P" => Proj 𝒜

private theorem moduleFinite_cohomology_free_tensor_twistingSheaf
    {κ : Type*} [Finite κ] [Nontrivial κ] (b : Basis κ R M)
    (I : Type u) [Finite I] (m : ℤ) (q : ℕ) :
    Module.Finite R (Cohomology
      ((SheafOfModules.free I : Scheme.Modules P) ⊗ Proj.twistingSheaf 𝒜 m) q) := by
  classical
  have := Fintype.ofFinite I
  have : HasFiniteBiproducts (Scheme.Modules P) := Abelian.hasFiniteBiproducts
  let L := Proj.twistingSheaf 𝒜 m
  let U := 𝟙_ (Scheme.Modules P)
  let T := tensorRight L
  let e := (T.mapIso (TauCeti.SheafOfModules.biproductIsoFree (R := (P).sheaf) I).symm) ≪≫
    Functor.mapBiproduct T (fun _ : I ↦ U) ≪≫ biproduct.mapIso (fun _ : I ↦ λ_ L)
  have := b.finite_cohomology_twistingSheaf m q
  exact Module.Finite.equiv
    (((cohomologyBaseLinearEquivOfIso R e q).trans
      (cohomologyBiproductLinearEquiv R (fun _ : I ↦ L) q)).symm)

/-- On projective space over a Noetherian ring, the cohomology of a quasi-coherent sheaf
of finite type is finitely generated in every degree. The basis has at least two elements. -/
private theorem moduleFinite_cohomology_proj [IsNoetherianRing R]
    {κ : Type*} [Finite κ] [Nontrivial κ] (b : Basis κ R M)
    (F : Scheme.Modules P) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  classical
  have := Fintype.ofFinite κ
  have : Module.Finite R M := Module.Finite.of_basis b
  revert F
  refine Nat.decreasingInduction'
    (motive := fun j ↦ ∀ (F : Scheme.Modules P) [F.IsQuasicoherent] [F.IsFiniteType],
      Module.Finite R (Cohomology F j))
    (n := max (Fintype.card κ) q) ?_ (le_max_right _ _) ?_
  · intro j _ _ ih F _ _
    let x : κ → SymmetricAlgebra R M := SymmetricAlgebra.ι R M ∘ b
    have hx (i : κ) : x i ∈ 𝒜 1 := ι_mem_homogeneousSubmodule R M (b i)
    have hcover : ⨆ i, Proj.basicOpen 𝒜 (x i) = ⊤ := iSup_basicOpen_ι_eq_top R M b b.span_eq
    obtain ⟨m, I, hI, π, hπ⟩ :=
      (Proj.eventually_exists_epi_free_tensor_twistingSheaf x hx hcover F).exists
    let S : ShortComplex (Scheme.Modules P) := ShortComplex.kernelSequence π
    have hS : S.ShortExact := TauCeti.kernelSequence_shortExact π
    let G : Scheme.Modules P := SheafOfModules.free I
    let L := Proj.twistingSheaf 𝒜 (-(m : ℤ))
    have : G.IsFinitePresentation := TauCeti.SheafOfModules.isFinitePresentation_free I
    have : L.IsFinitePresentation := isFinitePresentation_of_isInvertible L
    have : (G ⊗ L).IsQuasicoherent := isQuasicoherent_tensorObj P G L
    have : (G ⊗ L).IsFiniteType := isFiniteType_tensorObj G L
    let K : Scheme.Modules P := kernel π
    have : K.IsFinitePresentation := isFinitePresentation_kernel π
    have hKqc : K.IsQuasicoherent := isQuasicoherent_of_isFinitePresentation K
    have hKft : K.IsFiniteType := isFiniteType_of_isFinitePresentation K
    have : Module.Finite R (Cohomology S.X₂ j) :=
      b.moduleFinite_cohomology_free_tensor_twistingSheaf I (-(m : ℤ)) j
    have : Module.Finite R (Cohomology S.X₁ (j + 1)) := @ih K hKqc hKft
    exact (exact_cohomologyMapBaseLinear_cohomologyδBaseLinear R P hS j).moduleFinite
  · intro F _ _
    have := b.subsingleton_cohomology_proj_of_card_le F (max (Fintype.card κ) q)
      (le_max_left _ _)
    infer_instance

end Module.Basis

namespace AlgebraicGeometry.Scheme.Modules

/-- **Finiteness of coherent cohomology on projective schemes.** If `X` is projective
over a Noetherian ring `R`, the cohomology of every quasi-coherent sheaf of finite type on `X`
is finitely generated over `R` in every degree. -/
public theorem moduleFinite_cohomology_of_isProjectiveOver (R : Type u) [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))] [X.IsProjectiveOver R]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (q : ℕ) :
    Module.Finite R (Cohomology F q) := by
  obtain ⟨M, _, _, _, i, hi, hiR⟩ := Scheme.IsProjectiveOver.exists_isClosedImmersion (R := R)
    (X := X)
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  -- Two extra coordinates ensure that the ambient projective space has positive dimension.
  let res := LinearMap.funLeft R R (Fin.castLE (Nat.le_add_right n 2))
  let g := f.comp res
  have hg : Function.Surjective g :=
    hf.comp (LinearMap.funLeft_surjective_of_injective R R _ (Fin.castLE_injective _))
  let φ := SymmetricAlgebra.gradedMap R g
  have hφ : Function.Surjective φ := by
    simpa only [φ, Function.Surjective, SymmetricAlgebra.gradedMap_apply] using
      SymmetricAlgebra.map_surjective R g hg
  let hφirr := HomogeneousIdeal.irrelevant_le_map_of_surjective φ hφ
  have : IsClosedImmersion (Proj.map φ hφirr) := Proj.isClosedImmersion_map φ hφirr hφ
  have : (Proj.map φ hφirr).IsOver (Spec (.of R)) := ⟨Proj.map_gradedMap_projToSpec R g hφirr⟩
  let j := i ≫ Proj.map φ hφirr
  have : IsClosedImmersion j := inferInstanceAs (IsClosedImmersion (i ≫ Proj.map φ hφirr))
  have : j.IsOver (Spec (.of R)) := inferInstanceAs ((i ≫ Proj.map φ hφirr).IsOver (Spec (.of R)))
  exact (j.moduleFinite_cohomology_pushforward_iff R F q).mp
    ((Pi.basisFun R (Fin (n + 2))).moduleFinite_cohomology_proj ((pushforward j).obj F) q)

end AlgebraicGeometry.Scheme.Modules
