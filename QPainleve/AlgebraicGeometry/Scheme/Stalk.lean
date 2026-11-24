/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.AlgebraicGeometry.Scheme.BaseAlgebra
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent
import TauCeti.AlgebraicGeometry.Pullback.Carrier

/-!
# Stalk algebras and their spectra

On a scheme locally of finite type over an affine base, the canonical base algebra
on a stalk is essentially of finite type. Morphisms over the base induce algebra
homomorphisms between the stalks.
The spectrum of a stalk is flat over the scheme, and base changing to it
preserves every scheme mapping into its range.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical morphism from the spectrum of a stalk to the scheme is flat. -/
instance flat_fromSpecStalk (X : Scheme.{u}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk]
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  let := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Flat (Spec.map (X.presheaf.germ U x hxU)) := by
    rw [Flat.SpecMap_iff, ← X.presheaf.stalk_open_algebraMap ⟨x, hxU⟩,
      RingHom.flat_algebraMap_iff]
    exact IsLocalization.flat _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact Flat.comp _ _

/-- The canonical stalk algebra of a scheme locally of finite type over `Spec R` is essentially
of finite type over `R`. -/
theorem essFiniteType_stalk (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]
    [LocallyOfFiniteType (X ↘ Spec (.of R))] (x : X) :
    Algebra.EssFiniteType R (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let A := Γ(X, U)
  let : Algebra R A := ((X.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let : IsScalarTower R A (X.presheaf.stalk x) :=
    isScalarTower_base_section_stalk R X ⟨x, hxU⟩
  have : Algebra.FiniteType R A := finiteType_sections_of_locallyOfFiniteType R X ⟨U, hU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.EssFiniteType A (X.presheaf.stalk x) :=
    .of_isLocalization _ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact .comp R A _

/-- Base change to the spectrum of a stalk is an isomorphism on any scheme whose
image consists of generizations of the stalk's point. -/
theorem _root_.CategoryTheory.IsPullback.isIso_fst_of_fromSpecStalk
    {P X Y : Scheme.{u}} {y : Y} {f : X ⟶ Y}
    {a : P ⟶ X} {b : P ⟶ Spec (Y.presheaf.stalk y)}
    (h : IsPullback a b f (Y.fromSpecStalk y)) (hf : ∀ x : X, f x ⤳ y) : IsIso a := by
  have : IsPreimmersion a := MorphismProperty.of_isPullback h.flip inferInstance
  have : Flat a := MorphismProperty.of_isPullback h.flip inferInstance
  have : Surjective a := ⟨by
    rw [← Set.range_eq_univ, Pullback.range_fst_of_isPullback h, range_fromSpecStalk]
    exact Set.eq_univ_of_forall hf⟩
  have ha : IsHomeomorph a.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨a.isEmbedding, a.surjective⟩
  have : QuasiCompact a := ⟨fun U _ hU ↦ ha.homeomorph.isCompact_preimage.mpr hU⟩
  exact Flat.isIso_of_surjective_of_mono a

namespace Hom

/-- The stalk map of a morphism over an affine base, as a homomorphism of base algebras. -/
noncomputable def stalkMapAlgHom {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] (x : X) :
    Y.presheaf.stalk (f x) →ₐ[k] X.presheaf.stalk x where
  __ := (f.stalkMap x).hom
  commutes' r := by
    have h := SpecMap_stalkMap_fromSpecStalk f (x := x)
    have he := congrArg (fun g ↦ g ≫ (Y ↘ Spec (.of k))) h
    simp only [Category.assoc, comp_over, fromSpecStalk_comp_over, ← Spec.map_comp,
      Spec.map_inj] at he
    exact congrArg (fun g : CommRingCat.of k ⟶ _ ↦ g r) he

/-- The underlying ring homomorphism is the stalk map of the scheme morphism. -/
@[simp]
theorem stalkMapAlgHom_toRingHom {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] (x : X) :
    (f.stalkMapAlgHom (k := k) x : _ →+* _) = (f.stalkMap x).hom := (rfl)

/-- The stalk algebra homomorphism has the same values as the scheme stalk map. -/
@[simp]
theorem stalkMapAlgHom_apply {k : Type u} [CommRing k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] (f : X ⟶ Y)
    [f.IsOver (Spec (.of k))] (x : X) (a : Y.presheaf.stalk (f x)) :
    f.stalkMapAlgHom (k := k) x a = f.stalkMap x a := (rfl)

end Hom

end AlgebraicGeometry.Scheme
