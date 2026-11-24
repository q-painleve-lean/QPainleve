/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalSections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.TensorProduct

/-!
# Products of global sections on projective space

The global sections of two nonnegative twists generate the sections of their tensor
product by pure tensors. The comparison with homogeneous forms identifies these
products with ordinary polynomial multiplication.
-/

public section

open AlgebraicGeometry CategoryTheory Functor.LaxMonoidal MonoidalCategory
open Scheme.Modules TauCeti.SymmetricAlgebra

universe u v

namespace Module.Basis

variable {R M : Type u} [CommRing R] [AddCommMonoid M] [Module R M]
  {ι : Type v} [Nontrivial ι]

local notation "𝒜" => homogeneousSubmodule R M
local notation "T" => Proj.twistingSheaf 𝒜

/-- Every global section of `𝒪(m) ⊗ 𝒪(n)` on projective space is a sum of pure
tensors of global sections when both twists have nonnegative degree. -/
theorem surjective_sectionsFunctor_μ_twistingSheaf (b : Module.Basis ι R M) (m n : ℕ) :
    Function.Surjective (μ (sectionsFunctor ⊤) (T m) (T n)) := by
  let f := _root_.SymmetricAlgebra.ι R M
  let hcover := iSup_basicOpen_ι_eq_top R M id (by simp)
  let e := Proj.twistingSheaf.tensorObjIso f (ι_mem_homogeneousSubmodule R M)
    hcover (m : ℤ) (n : ℤ)
  let t := μ (sectionsFunctor ⊤) (T m) (T n)
  have hinj : Function.Injective (e.hom.app ⊤) :=
    (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  intro s
  have hcast : ((m + n : ℕ) : ℤ) = (m : ℤ) + n := Nat.cast_add _ _
  let d := Proj.toTwistingSheaf 𝒜 hcast ⊤
  have hd : Function.Surjective d := (bijective_toTwistingSheaf_top (m + n) b).surjective
  obtain ⟨p, hp⟩ := hd (e.hom.app ⊤ s)
  have hm : (p : _root_.SymmetricAlgebra R M) ∈ 𝒜 m * 𝒜 n := by
    rw [← pow_add]
    exact p.property
  let u := (e.hom.app ⊤).hom.comp t.hom.toAddMonoidHom
  let P := AddMonoidHom.range u
  suffices hh : d p ∈ P by
    obtain ⟨z, hz⟩ := (AddMonoidHom.mem_range (f := u)).mp hh
    exact ⟨z, hinj (hz.trans hp)⟩
  -- Use the homogeneous degree of each summand to apply the section map.
  refine Submodule.mul_induction_on' (C := fun q hq ↦
    d ⟨q, by simpa only [← pow_add] using hq⟩ ∈ P) ?_ ?_ hm
  · intro x hx y hy
    let x' := Proj.toTwistingSheaf 𝒜 (rfl : (m : ℤ) = m) ⊤ ⟨x, hx⟩
    let y' := Proj.toTwistingSheaf 𝒜 (rfl : (n : ℤ) = n) ⊤ ⟨y, hy⟩
    refine ⟨TensorProduct.tmul _ x' y', ?_⟩
    have hmul := Proj.twistingSheaf.tensorObjIso_hom_app_tmulRight f
      (ι_mem_homogeneousSubmodule R M) hcover (m : ℤ) (n : ℤ) ⊤ x' y'
    rw [tmulRight_apply] at hmul
    exact hmul.trans (Proj.mul_toTwistingSheaf rfl rfl ⊤ ⟨x, hx⟩ ⟨y, hy⟩)
  · intro x hx y hy h₁ h₂
    have hadd := map_add d (⟨x, by simpa only [← pow_add] using hx⟩)
      (⟨y, by simpa only [← pow_add] using hy⟩)
    exact hadd ▸ P.add_mem h₁ h₂

end Module.Basis
