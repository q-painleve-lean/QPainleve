/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Linear
public import QPainleve.AlgebraicGeometry.Modules.FiniteSupport

/-!
# Cohomology of a sheaf with finite support

On a scheme locally of finite type over a field, a finite type quasi-coherent sheaf with
finite support comes from its scheme-theoretic support, which is finite over the field.
Its cohomology is finite-dimensional and vanishes in positive degrees. The Euler
characteristic is the sum of the stalk lengths weighted by residue degrees. It is preserved
by tensoring with a line bundle.

## References

* The Stacks Project, Lemma 33.33.3 (Tag 0AYT).
-/

public section

open CategoryTheory MonoidalCategory
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]
  (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]

include k in
/-- A finite type quasi-coherent sheaf with finite support has no positive-degree cohomology. -/
theorem subsingleton_cohomology_succ_of_finite_support
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) (n : ℕ) :
    Subsingleton (Cohomology M (n + 1)) := by
  obtain ⟨Z, i, _, _, ⟨e⟩⟩ := exists_iso_pushforward_of_finite_support k M h
  have := subsingleton_cohomology_succ_of_isAffineHom
    (i ≫ (X ↘ Spec (.of k))) ((pullback i).obj M) n
  let comparison := (cohomologyFunctor X (n + 1)).mapIso e ≪≫
    cohomologyPushforwardIso i ((pullback i).obj M) (n + 1)
  exact comparison.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

/-- Every cohomology group of a finite type quasi-coherent sheaf with finite support is
finite-dimensional over the base field. -/
theorem finiteDimensional_cohomology_of_finite_support
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) (n : ℕ) :
    FiniteDimensional k (Cohomology M n) := by
  cases n with
  | succ n =>
    have := subsingleton_cohomology_succ_of_finite_support k M h n
    infer_instance
  | zero =>
    obtain ⟨Z, i, _, _, ⟨e⟩⟩ := exists_iso_pushforward_of_finite_support k M h
    let f : Z ⟶ Spec (.of k) := i ≫ (X ↘ Spec (.of k))
    let : Z.Over (Spec (.of k)) := ⟨f⟩
    have : i.IsOver (Spec (.of k)) := ⟨rfl⟩
    let G := (pullback i).obj M
    have : IsAffine Z := isAffine_of_isAffineHom f
    let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    have : Module.Finite k Γ(Z, ⊤) := f.moduleFinite_appTop rfl
    have : Module.Finite Γ(Z, ⊤) Γ(G, ⊤) :=
      G.finite_sections_of_isAffineOpen ⊤ (isAffineOpen_top Z)
    have : IsScalarTower k Γ(Z, ⊤) Γ(G, ⊤) :=
      .of_algebraMap_smul fun r m ↦ by
        simp only [base_smul_globalSections, baseRingToGlobalSections_apply,
          RingHom.algebraMap_toAlgebra]
        rfl
    have : Module.Finite k Γ(G, ⊤) := Module.Finite.trans Γ(Z, ⊤) _
    let comparison := (cohomologyBaseLinearEquivOfIso k e 0).trans
      ((i.cohomologyPushforwardBaseLinearEquiv k G 0).trans
        (cohomologyZeroBaseLinearEquiv k Z G))
    exact Module.Finite.equiv comparison.symm

/-- For a finite type quasi-coherent sheaf with finite support, every positive truncation of
the Euler characteristic equals the dimension of its space of global sections. -/
theorem eulerCharBelow_succ_of_finite_support
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) (n : ℕ) :
    eulerCharBelow k X M (n + 1) = (Module.finrank k Γ(M, ⊤) : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := subsingleton_cohomology_succ_of_finite_support k M h n
    rw [eulerCharBelow_succ k M (n + 1), ih]
    simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero, add_zero]

/-- The Euler characteristic of a finite-support sheaf is the sum of its stalk lengths weighted
by residue degrees. Every positive truncation gives the same value. -/
theorem eulerCharBelow_succ_eq_sum_length_mul_of_finite_support
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) (n : ℕ) :
    eulerCharBelow k X M (n + 1) =
      ∑ᶠ x : {x : X // Nontrivial (M.presheaf.stalk x)},
        (Module.length (X.presheaf.stalk (x : X)) (M.presheaf.stalk (x : X))).toNat *
          (Module.finrank k (X.residueField (x : X)) : ℤ) := by
  let S := {x : X | Nontrivial (M.presheaf.stalk x)}
  let : Fintype S := h.fintype
  let e := globalSectionsGermsLinearEquiv M k h
    (fun x hx ↦ isClosed_singleton_of_finite_support k M h hx)
    (fun _ hx ↦ not_nontrivial_iff_subsingleton.mp hx)
  have : Module.Finite k Γ(M, ⊤) := by
    have := finiteDimensional_cohomology_of_finite_support k M h 0
    exact Module.Finite.equiv (cohomologyZeroBaseLinearEquiv k X M)
  have (x : S) : Module.Finite k (M.presheaf.stalk x) :=
    Module.Finite.of_surjective ((LinearMap.proj x).comp e.toLinearMap)
      ((Function.surjective_eval x).comp e.surjective)
  rw [eulerCharBelow_succ_of_finite_support k M h, e.finrank_eq, Module.finrank_pi_fintype,
    finsum_eq_sum_of_fintype]
  push_cast
  simp only [finrank_stalk_eq_length_mul, Nat.cast_mul]
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext x
  simp

/-- Over an algebraically closed field every closed point has residue degree one, so the
Euler characteristic of a finite-support sheaf is the sum of the local lengths. -/
theorem eulerCharBelow_succ_eq_sum_length_of_finite_support [IsAlgClosed k]
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) (n : ℕ) :
    eulerCharBelow k X M (n + 1) =
      ∑ᶠ x : {x : X // Nontrivial (M.presheaf.stalk x)},
        ((Module.length (X.presheaf.stalk (x : X)) (M.presheaf.stalk (x : X))).toNat : ℤ) := by
  rw [eulerCharBelow_succ_eq_sum_length_mul_of_finite_support k M h]
  refine finsum_congr fun x ↦ ?_
  have hx := isClosed_singleton_of_finite_support k M h x.property
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hf : LocallyOfFiniteType (X.fromSpecResidueField x ≫ (X ↘ Spec (.of k))) := inferInstance
  rw [Scheme.fromSpecResidueField_comp_over] at hf
  have : Algebra.FiniteType k (X.residueField x) := by
    rwa [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom,
      RingHom.finiteType_algebraMap] at hf
  have : Module.Finite k (X.residueField x) := finite_of_finite_type_of_isJacobsonRing k _
  let e : k ≃ₐ[k] X.residueField x :=
    AlgEquiv.ofBijective (Algebra.ofId k _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hr : Module.finrank k (X.residueField x) = 1 :=
    e.toLinearEquiv.finrank_eq.symm.trans (Module.finrank_self k)
  simp [hr]

/-- Twisting a finite type quasi-coherent sheaf of finite support by a line bundle preserves
its Euler characteristic at every truncation. -/
theorem eulerCharBelow_tensor_left_of_finite_support
    (h : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) (L : InvertibleSheaf X) (n : ℕ) :
    eulerCharBelow k X (L.obj ⊗ M) n = eulerCharBelow k X M n :=
  (nonempty_iso_tensor_left_of_finite_support k M h L).elim fun e ↦ eulerCharBelow_congr k e n

end AlgebraicGeometry.Scheme.Modules
