/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Fibers.Composition

import QPainleve.AlgebraicGeometry.Fiber
import QPainleve.AlgebraicGeometry.Morphisms.Finite
import QPainleve.RingTheory.LocalProperties.Fiber
import TauCeti.AlgebraicGeometry.ResidueField

/-!
# Closed fibers of proper morphisms

Over a quasi-compact Jacobson target, a proper morphism is a closed immersion
if its fibers over closed points are closed subschemes of the corresponding
residue spectra. For a reduced target, this also gives a way to recognize an
isomorphism over a base from isomorphisms on closed fibers of the base.

The proper-to-finite step uses `isFinite_iff_forall_isClosed_finite_preimage_singleton`,
the closed-point form of [Stacks Project, Lemma 30.21.2](https://stacks.math.columbia.edu/tag/02OH).
On affine opens, Nakayama's lemma detects the surjectivity of the coordinate map
from the residue rings at closed points.
-/

public section

open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y S : Scheme.{u}}

private theorem isClosedImmersion_specMap_of_closed_fibers {A B : CommRingCat.{u}}
    (f : A ⟶ B) [IsFinite (Spec.map f)]
    (h : ∀ y : Spec A, IsClosed ({y} : Set (Spec A)) →
      IsClosedImmersion ((Spec.map f).fiberToSpecResidueField y)) :
    IsClosedImmersion (Spec.map f) := by
  let := f.hom.toAlgebra
  have : Module.Finite A B := (IsFinite.SpecMap_iff f).mp inferInstance
  apply IsClosedImmersion.spec_of_surjective f
  apply LinearMap.surjective_of_lTensor_residueField_maximal (Algebra.linearMap A B)
  intro m hm x
  let y : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  have hy : IsClosed ({y} : Set (Spec A)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hm
  let φ := CommRingCat.ofHom (algebraMap m.ResidueField (m.Fiber B))
  have : IsClosedImmersion (Spec.map φ) := (MorphismProperty.arrow_mk_iso_iff
    @IsClosedImmersion (Spec.fiberToSpecResidueFieldIso A B y)).mp (h y hy)
  have hsurj := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map φ)).2
  have hφ : φ = (Scheme.ΓSpecIso _).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso _).hom := by
    simp
  have hs : Function.Surjective φ.hom := by
    rw [hφ, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso _).surjective.comp
      (hsurj.comp (ConcreteCategory.bijective_of_isIso _).surjective)
  obtain ⟨a, ha⟩ := hs x
  exact ⟨a ⊗ₜ[A] (1 : A), by simpa [φ, Algebra.TensorProduct.algebraMap_def] using ha⟩

/-- A proper morphism to a quasi-compact Jacobson scheme is a closed immersion
if the structural morphisms of its closed fibers are closed immersions. -/
theorem isClosedImmersion_of_isClosedImmersion_closed_fibers
    (f : X ⟶ Y) [IsProper f] [CompactSpace Y] [JacobsonSpace Y]
    (h : ∀ y : Y, IsClosed ({y} : Set Y) → IsClosedImmersion (f.fiberToSpecResidueField y)) :
    IsClosedImmersion f := by
  have : IsFinite f := f.isFinite_iff_forall_isClosed_finite_preimage_singleton.mpr fun y hy ↦ by
    let := h y hy
    let : Subsingleton (f.fiber y) :=
      (f.fiberToSpecResidueField y).isClosedEmbedding.injective.subsingleton
    exact Set.finite_coe_iff.mp (Finite.of_equiv (f.fiber y) (f.fiberHomeo y).toEquiv)
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) Y.affineCover).mpr
    fun a ↦ ?_
  let j := Y.affineCover.f a
  have : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (Y.affineCover.f a))
  let F := pullback.snd f j
  have : IsAffine (pullback f j) := isAffine_of_isAffineHom F
  let e := (pullback f j).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ F)
  -- The cover morphism is the second projection of this affine base change.
  change IsClosedImmersion F
  apply (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.inv F).mp
  refine hφ ▸ ?_
  have : IsFinite (Spec.map φ) := hφ ▸ inferInstanceAs (IsFinite (e.inv ≫ F))
  refine isClosedImmersion_specMap_of_closed_fibers φ fun y hy ↦ ?_
  have hj : IsClosed ({j y} : Set Y) := by
    have hy' : y ∈ closedPoints (Y.affineCover.X a) := hy
    rwa [← j.isOpenEmbedding.preimage_closedPoints] at hy'
  have H : IsPullback ((e.inv ≫ pullback.fst f j)) (Spec.map φ) f j := by
    rw [hφ]
    exact (IsPullback.of_hasPullback f j).of_iso e (.refl _) (.refl _) (.refl _)
      (by simp) ((Category.comp_id F).trans (e.hom_inv_id_assoc F).symm)
      (by simp) (Category.id_comp j).symm
  have hres : IsIso (j.residueFieldMap (y : Y.affineCover.X a)) :=
    Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks j y
  obtain ⟨E⟩ := @IsPullback.nonempty_iso_fiberToSpecResidueField _ _ _ _ _ _ _ _ H y hres
  have hEq : E.hom.left ≫ f.fiberToSpecResidueField (j y) =
      (Spec.map φ).fiberToSpecResidueField y ≫ Spec.map (j.residueFieldMap y) := Over.w E.hom
  have : IsClosedImmersion (f.fiberToSpecResidueField (j y)) := h _ hj
  have : IsClosedImmersion (E.hom.left ≫ f.fiberToSpecResidueField (j y)) := inferInstance
  rw [hEq] at this
  exact .of_comp _ (Spec.map (j.residueFieldMap y))

/-- A proper morphism of schemes over a base is an isomorphism if it induces an
isomorphism on every fiber over a closed point of that base, provided the target
is quasi-compact, Jacobson and reduced, and its structure map sends closed
points to closed points. -/
theorem isIso_of_isIso_fiberCompMap_of_isClosed
    (f : X ⟶ Y) (g : Y ⟶ S) [IsProper f] [CompactSpace Y] [JacobsonSpace Y] [IsReduced Y]
    (hg : Set.MapsTo g (closedPoints Y) (closedPoints S))
    (h : ∀ s : S, IsClosed ({s} : Set S) → IsIso (f.fiberCompMap g s)) :
    IsIso f := by
  have hclosed (y : Y) (hy : IsClosed ({y} : Set Y)) : IsIso (f.fiberToSpecResidueField y) := by
    have hs : IsClosed ({g y} : Set S) := hg hy
    let := h (g y) hs
    let z := g.asFiber y
    let k := f.fiberCompMap g (g y)
    have hk : IsIso (k.fiberToSpecResidueField z) :=
      inferInstanceAs (IsIso (pullback.snd k ((g.fiber (g y)).fromSpecResidueField z)))
    obtain ⟨E⟩ := (f.isPullback_fiberCompMap g (g y)).flip.nonempty_iso_fiberToSpecResidueField z
    have hEq : E.inv.left ≫
        (k.fiberToSpecResidueField z ≫ Spec.map ((g.fiberι (g y)).residueFieldMap z)) =
        f.fiberToSpecResidueField ((g.fiberι (g y)) z) := Over.w E.inv
    have hIso : IsIso (E.inv.left ≫
        (k.fiberToSpecResidueField z ≫ Spec.map ((g.fiberι (g y)).residueFieldMap z))) :=
      inferInstance
    rwa [hEq, fiberι_asFiber] at hIso
  let : IsClosedImmersion f := f.isClosedImmersion_of_isClosedImmersion_closed_fibers
    fun y hy ↦ by let := hclosed y hy; infer_instance
  have hmem (y : Y) (hy : y ∈ closedPoints Y) : y ∈ Set.range f := by
    let := hclosed y hy
    let z := (CategoryTheory.inv (f.fiberToSpecResidueField y)) (IsLocalRing.closedPoint _)
    exact ⟨f.fiberι y z, by
      have hz : f.fiberι y z ∈ Set.range (f.fiberι y) := ⟨z, rfl⟩
      rw [f.range_fiberι] at hz
      exact hz⟩
  have : Surjective f := ⟨fun y ↦ by
    have hr := closure_minimal (fun y hy ↦ hmem y hy) f.isClosedMap.isClosed_range
    rw [closure_closedPoints] at hr
    exact hr (Set.mem_univ y)⟩
  exact isIso_of_isClosedImmersion_of_surjective f

end AlgebraicGeometry.Scheme.Hom
