/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.AlgebraicGeometry.RationalMap.Composition.Defined
public import TauCeti.Algebra.MvPolynomial.Laurent.Basic

import QPainleve.AlgebraicGeometry.RationalMap.Restriction

/-!
# Regular charts for the rational X maps of cluster steps

The chart inverting the pivot binomial is a domain for the mutation rational map.
Relabeling is regular on the entire torus. These comparisons allow evaluation at
points with nondense image, for example the generic point of a fixed-center toric surface.
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.Cluster QPainleve.CharacterTorus
open TauCeti LaurentRing

namespace Quiver.Path

universe u

variable {ι : Type u} [Finite ι] [DecidableEq ι] {B C : SkewExchangeMatrix ι}
  (k : Type u) [Field k]

local notation "L" => LaurentRing k ι
local notation "Xtor" => scheme k (ι →₀ ℤ)
local notation "K" => FractionRing L
local notation "aff" => affineFractionRingEquiv k (ι →₀ ℤ)

private theorem exists_lift_of_xPullback (w : Word B C) {R : Type u} [CommRing R]
    (a m : L →+* R) (d : R →+* K)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom a))]
    (ha : d.comp a = algebraMap L K)
    (hm : d.comp m = (w.xPullback k).toRingHom.comp (algebraMap L K)) :
    let f := w.xRationalMap k
    ∃ l : Spec (.of R) ⟶ f.toPartialMap.domain,
      l ≫ f.toPartialMap.domain.ι = Spec.map (CommRingCat.ofHom a) ∧
      l ≫ f.toPartialMap.hom = Spec.map (CommRingCat.ofHom m) := by
  intro f
  let η := Spec.map (CommRingCat.ofHom ((aff).toRingHom.comp d))
  have hη : η ≫ Spec.map (CommRingCat.ofHom a) = (Xtor).fromSpecStalk (genericPoint Xtor) := by
    apply Spec.preimage_injective
    apply CommRingCat.hom_ext
    dsimp only [η]
    rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map, CommRingCat.hom_comp,
      preimage_fromSpecStalk]
    simp only [CommRingCat.hom_ofHom, RingHom.comp_assoc, ha]
  have hvalue : η ≫ Spec.map (CommRingCat.ofHom m) = f.fromFunctionField := by
    apply Spec.preimage_injective
    apply CommRingCat.hom_ext
    have h := affineRationalPullback_comp_algebraMap (w.xRationalMap k)
    rw [affineRationalPullback_xRationalMap] at h
    dsimp only [η]
    rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map, CommRingCat.hom_comp]
    simp only [CommRingCat.hom_ofHom, RingHom.comp_assoc, hm, h]
    rw [← RingHom.comp_assoc]
    simp [f]
  exact f.exists_lift_of_fromFunctionField_eq _ _ η hη hvalue

/-- The open chart inverting the pivot binomial factors through the domain of the
one-step mutation, whose restriction is the chart isomorphism followed by inclusion. -/
theorem exists_lift_xRationalMap_mutate (B : SkewExchangeMatrix ι) (p : ι) :
    let a := algebraMap L (XMutationChart k p)
    let m := (xMutationChartEquiv k p (fun j ↦ B.matrix j p)).toRingHom.comp a
    let f := ((Generator.mutate p).toStep B).toPath.xRationalMap k
    ∃ l : Spec (.of (XMutationChart k p)) ⟶ f.toPartialMap.domain,
      l ≫ f.toPartialMap.domain.ι = Spec.map (CommRingCat.ofHom a) ∧
      l ≫ f.toPartialMap.hom = Spec.map (CommRingCat.ofHom m) := by
  intro a m f
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom a)) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of L) (1 + X p)
  apply exists_lift_of_xPullback k _ a m (xMutationChartToFunctionField k p).toRingHom
  · apply RingHom.ext
    intro x
    exact xMutationChartToFunctionField_algebraMap k p x
  · apply RingHom.ext
    intro x
    rw [xPullback_toPath, Step.xPullback_toStep, Generator.xPullback_mutate]
    -- Both ring homomorphisms are the underlying maps of the chart algebra homomorphisms.
    change xMutationChartToFunctionField k p
      (xMutationChartEquiv k p (fun j ↦ B.matrix j p) (a x)) =
      xMutation k p (fun j ↦ B.matrix j p) (algebraMap L K x)
    rw [← xMutation_xMutationChartToFunctionField, xMutationChartToFunctionField_algebraMap]

/-- An evaluation into the pivot chart can be followed by rational X mutation.
The composite is obtained by applying the chart isomorphism and including the result
in the independent X torus. -/
theorem compOfDefined_xRationalMap_mutate {X : Scheme.{u}} [IsIntegral X]
    (B : SkewExchangeMatrix ι) (p : ι) (a : X ⤏ Spec (.of (XMutationChart k p))) :
    let i := Spec.algebraMap L (XMutationChart k p)
    let f := ((Generator.mutate p).toStep B).toPath.xRationalMap k
    let e := Spec.map (CommRingCat.ofHom
      (xMutationChartEquiv k p (fun j ↦ B.matrix j p)).toAlgHom.toRingHom)
    ∃ h : (a.compHom i).fromFunctionField (IsLocalRing.closedPoint X.functionField) ∈ f.domain,
      (a.compHom i).compOfDefined f h = (a.compHom e).compHom i := by
  intro i f e
  obtain ⟨l, hl, hl'⟩ := exists_lift_xRationalMap_mutate k B p
  have hi : Spec.map (CommRingCat.ofHom (algebraMap L (XMutationChart k p))) = i := (rfl)
  have hm : l ≫ f.toPartialMap.hom = e ≫ i := by
    rw [hl', ← hi, ← Spec.map_comp]
    rfl
  let g := a.fromFunctionField ≫ l
  have hg : g ≫ f.toPartialMap.domain.ι = (a.compHom i).fromFunctionField := by
    rw [Scheme.RationalMap.fromFunctionField_compHom, Category.assoc, hl, hi]
  have h : (a.compHom i).fromFunctionField
      (IsLocalRing.closedPoint X.functionField) ∈ f.domain := by
    let x : Spec X.functionField := IsLocalRing.closedPoint X.functionField
    rw [← f.toPartialMap_domain, ← congrArg (fun m : Spec X.functionField ⟶ Xtor ↦ m x) hg]
    exact (g x).property
  refine ⟨h, Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  rw [Scheme.RationalMap.fromFunctionField_compOfDefined _ _ h g hg,
    Scheme.RationalMap.fromFunctionField_compHom, Scheme.RationalMap.fromFunctionField_compHom,
    Category.assoc, hm, Category.assoc]

/-- A relabeling acts regularly on the entire X torus by renaming its Laurent coordinates. -/
theorem exists_lift_xRationalMap_permute (B : SkewExchangeMatrix ι) (σ : Equiv.Perm ι) :
    let f := ((Generator.permute σ).toStep B).toPath.xRationalMap k
    ∃ l : Xtor ⟶ f.toPartialMap.domain,
      l ≫ f.toPartialMap.domain.ι = 𝟙 Xtor ∧
      l ≫ f.toPartialMap.hom = Spec.map (CommRingCat.ofHom (rename (R := k) σ).toRingHom) := by
  intro f
  have hi : Spec.map (CommRingCat.ofHom (RingHom.id L)) = 𝟙 Xtor :=
    Spec.map_id (.of L)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.id L))) := hi ▸ inferInstance
  let e := AddMonoidAlgebra.domCongr k k (Finsupp.domCongr (M := ℤ) σ)
  have hrename : rename (R := k) σ = e.toAlgHom := by
    apply algHom_ext
    intro j
    simp [e, X_def]
  have hm : (algebraMap L K).comp (rename (R := k) σ).toRingHom =
      (((Generator.permute σ).toStep B).toPath.xPullback k).toRingHom.comp (algebraMap L K) := by
    rw [hrename, xPullback_toPath, Step.xPullback_toStep, Generator.xPullback_permute]
    apply RingHom.ext
    intro x
    exact (IsFractionRing.algEquivOfAlgEquiv_algebraMap e x).symm
  obtain ⟨l, hl, hl'⟩ := exists_lift_of_xPullback k ((Generator.permute σ).toStep B).toPath
    (RingHom.id L) (rename (R := k) σ).toRingHom (algebraMap L K) (RingHom.comp_id _) hm
  exact ⟨l, hl.trans hi, hl'⟩

/-- The rational map of a relabeling is the regular Laurent-coordinate renaming. -/
theorem xRationalMap_permute (B : SkewExchangeMatrix ι) (σ : Equiv.Perm ι) :
    ((Generator.permute σ).toStep B).toPath.xRationalMap k =
      (Spec.map (CommRingCat.ofHom (rename (R := k) σ).toRingHom)).toRationalMap := by
  let f := ((Generator.permute σ).toStep B).toPath.xRationalMap k
  let g := Spec.map (CommRingCat.ofHom (rename (R := k) σ).toRingHom)
  obtain ⟨l, hl, hl'⟩ : ∃ l : Xtor ⟶ f.toPartialMap.domain,
      l ≫ f.toPartialMap.domain.ι = 𝟙 Xtor ∧ l ≫ f.toPartialMap.hom = g :=
    exists_lift_xRationalMap_permute k B σ
  have hinv : f.toPartialMap.domain.ι ≫ l = 𝟙 _ := by
    apply (cancel_mono f.toPartialMap.domain.ι).mp
    simp only [Category.assoc, hl, Category.comp_id, Category.id_comp]
  have heq : f = g.toRationalMap := by
    rw [← f.toRationalMap_toPartialMap, Scheme.PartialMap.toRationalMap_eq_iff]
    apply (f.toPartialMap.equiv_toPartialMap_iff_of_isSeparated
      (Limits.terminal.from _) (Limits.terminal.from _) (by simp)).mpr
    rw [← hl', ← Category.assoc, hinv, Category.id_comp]
  exact heq

end Quiver.Path
