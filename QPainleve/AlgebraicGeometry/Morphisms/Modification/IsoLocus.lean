/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
public import TauCeti.AlgebraicGeometry.Scheme.Normal
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import QPainleve.Topology.NoetherianSpace
import TauCeti.AlgebraicGeometry.Birational.Irreducible
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Normalization.Basic
import TauCeti.AlgebraicGeometry.Normalization.IsIso
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.Topology.KrullDimension.Basic

/-!
# Isomorphism loci of proper birational morphisms

A modification with reduced source is an isomorphism at the valuation-ring stalks of its
integral target. If the target is normal, its isomorphism locus is the image of its quasi-finite
locus. For surfaces the centre is a finite set of closed points, and the prime divisors above
it form a finite set. These are the isomorphism and finiteness criteria used to choose point
blowups in a factorization of a proper birational morphism.

The proof uses Tau Ceti's `Scheme.Hom.isoLocus` and `Scheme.Hom.normalizationMap`, together with
Mathlib's relative form of Zariski's main theorem.

## References

* [The Stacks Project, Lemma 33.17.3](https://stacks.math.columbia.edu/tag/0BFP).
* [The Stacks Project, Lemma 54.17.1](https://stacks.math.columbia.edu/tag/0C5R).
-/

public section

open CategoryTheory Limits Order TopologicalSpace TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A dominant section of a separated morphism with reduced source is its inverse. -/
theorem isIso_of_dominant_section [IsReduced X] [IsSeparated f] (s : Y ⟶ X)
    [IsDominant s] (hs : s ≫ f = 𝟙 Y) : IsIso f := by
  have hinv : f ≫ s = 𝟙 X :=
    ext_of_isDominant_of_isSeparated f (by simp [hs]) s (by simp [reassoc_of% hs])
  exact ⟨⟨s, hinv, hs⟩⟩

/-- A dominant morphism from an open of the target giving a section there places that open
inside the isomorphism locus. -/
theorem le_isoLocus_of_dominant_section [IsReduced X] [IsSeparated f]
    {U : Y.Opens} (s : U.toScheme ⟶ X) [IsDominant s] (hs : s ≫ f = U.ι) :
    U ≤ f.isoLocus := by
  let H := (isPullback_morphismRestrict f U).flip
  let t := H.lift s (𝟙 U.toScheme) (by simpa using hs)
  have ht : t ≫ (f ⁻¹ᵁ U).ι = s := H.lift_fst _ _ _
  have : IsDominant (t ≫ (f ⁻¹ᵁ U).ι) := ht.symm ▸ inferInstanceAs (IsDominant s)
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t (f ⁻¹ᵁ U).ι
  exact f.le_isoLocus_iff.mpr <|
    (f ∣_ U).isIso_of_dominant_section t (H.lift_snd _ _ _)

/-- If a universally closed morphism locally of finite type has a dominant generic section,
it has a dominant section over a neighbourhood of each valuation-ring stalk of its
integral target. -/
theorem exists_dominant_section_over_open_of_valuationRing [IsIntegral Y] [UniversallyClosed f]
    [LocallyOfFiniteType f] (y : Y) [ValuationRing (Y.presheaf.stalk y)]
    (s : Spec Y.functionField ⟶ X) [IsDominant s]
    (hs : s ≫ f = Y.fromSpecStalk (genericPoint Y)) :
    ∃ (U : Y.Opens) (_ : y ∈ U) (g : U.toScheme ⟶ X), g ≫ f = U.ι ∧ IsDominant g := by
  have hsq : s ≫ f = Spec.map (CommRingCat.ofHom
      (algebraMap (Y.presheaf.stalk y) Y.functionField)) ≫ Y.fromSpecStalk y := by
    rw [hs, ← SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)]
    rfl
  let sq : ValuativeCommSq f :=
    { R := Y.presheaf.stalk y
      domain := inferInstanceAs (IsDomain (Y.presheaf.stalk y))
      valuationRing := ‹ValuationRing (Y.presheaf.stalk y)›
      K := Y.functionField
      i₁ := s
      i₂ := Y.fromSpecStalk y
      commSq := ⟨hsq⟩ }
  have hvc := ((UniversallyClosed.eq_valuativeCriterion.le _ _ f inferInstance).1) sq
  let l := hvc.exists_lift.some
  obtain ⟨U, hy, g, hl, hg⟩ :=
    spread_out_of_isGermInjective' (𝟙 Y) f (x := y) l.l (by simpa using l.fac_right)
  let i := Spec.map (CommRingCat.ofHom
    (algebraMap (Y.presheaf.stalk y) Y.functionField)) ≫ U.fromSpecStalkOfMem y hy
  have he : i ≫ g = s := by
    dsimp only [i]
    rw [Category.assoc, ← hl]
    exact l.fac_left
  have : IsDominant (i ≫ g) := he.symm ▸ ‹IsDominant s›
  exact ⟨U, hy, g, by simpa using hg, IsDominant.of_comp i g⟩

/-- A modification with irreducible target has a dominant section over the generic point
of the target. -/
theorem exists_dominant_generic_section [IrreducibleSpace Y] [IsModification f] :
    ∃ s : Spec Y.functionField ⟶ X,
      s ≫ f = Y.fromSpecStalk (genericPoint Y) ∧ IsDominant s := by
  obtain ⟨U, hU, hpre, hIso⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  obtain ⟨z, hz⟩ := hU.nonempty
  have hη : genericPoint Y ∈ U := (genericPoint_specializes z).mem_open U.isOpen hz
  let s := U.fromSpecStalkOfMem (genericPoint Y) hη ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι
  have hs : s ≫ f = Y.fromSpecStalk (genericPoint Y) := by
    simp [s, ← morphismRestrict_ι]
  have : IsDominant (f ⁻¹ᵁ U).ι := Opens.isDominant_ι hpre
  have : IsDominant (U.fromSpecStalkOfMem (genericPoint Y) hη ≫ U.ι) := by
    rw [Opens.fromSpecStalkOfMem_ι]
    infer_instance
  have : IsDominant (U.fromSpecStalkOfMem (genericPoint Y) hη) :=
    IsDominant.of_comp_of_isOpenImmersion _ U.ι
  have : IsDominant s := inferInstanceAs (IsDominant (_ ≫ inv (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι))
  exact ⟨s, hs, ‹IsDominant s›⟩

/-- A modification of integral schemes is an isomorphism near any point of the target
whose local ring is a valuation ring. -/
theorem mem_isoLocus_of_valuationRing [IsReduced X] [IsIntegral Y] [IsModification f]
    (y : Y) [ValuationRing (Y.presheaf.stalk y)] : y ∈ f.isoLocus := by
  obtain ⟨s, hs, hdom⟩ := f.exists_dominant_generic_section
  obtain ⟨V, hy, g, hg, hdom'⟩ := f.exists_dominant_section_over_open_of_valuationRing y s hs
  exact f.le_isoLocus_of_dominant_section g hg hy

/-- The relative normalization along a modification of integral schemes with normal target
is isomorphic to the target. -/
theorem isIso_fromNormalization_of_isModification [IsReduced X] [IsIntegral Y]
    [IsNormalScheme Y] [IsModification f] : IsIso f.fromNormalization := by
  let g := Y.fromSpecStalk (genericPoint Y)
  have hg : IsIso g.fromNormalization := by
    refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
      (P := MorphismProperty.isomorphisms _) (f := g.fromNormalization) fun y ↦ ?_
    obtain ⟨U, hU, hy, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top y)
    have : Nonempty U := ⟨⟨y, hy⟩⟩
    have := IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hU
    exact ⟨U, hy, isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosed hU⟩
  obtain ⟨s, hs, hdom⟩ := f.exists_dominant_generic_section
  let m := g.normalizationMap f s hs
  have hcomp : g.toNormalization ≫ m = s ≫ f.toNormalization :=
    g.toNormalization_normalizationMap f s hs
  have : IsDominant (g.toNormalization ≫ m) :=
    hcomp.symm ▸ inferInstanceAs (IsDominant (s ≫ f.toNormalization))
  have : IsDominant m := IsDominant.of_comp g.toNormalization m
  refine f.fromNormalization.isIso_of_dominant_section (inv g.fromNormalization ≫ m) ?_
  rw [Category.assoc, g.normalizationMap_fromNormalization, IsIso.inv_hom_id]

/-- A modification of integral schemes with normal target is an isomorphism over a
neighbourhood of any point with a quasi-finite point in its fibre. -/
theorem mem_isoLocus_of_quasiFiniteAt [IsReduced X] [IsIntegral Y] [IsNormalScheme Y]
    [IsModification f] {x : X} (hx : f.QuasiFiniteAt x) : f x ∈ f.isoLocus := by
  let U := f.quasiFiniteLocus
  let g := U.ι ≫ f
  have := f.isIso_fromNormalization_of_isModification
  have : IsOpenImmersion g := by
    have h : g = (U.ι ≫ f.toNormalization) ≫ f.fromNormalization := by
      simp [g]
    have hOpen : IsOpenImmersion ((U.ι ≫ f.toNormalization) ≫ f.fromNormalization) :=
      inferInstance
    exact h.symm ▸ hOpen
  have := (IsModification.birational f).irreducibleSpace
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, f.mem_quasiFiniteLocus.mpr hx⟩)
  let s := g.isoOpensRange.inv ≫ U.ι
  have hs : s ≫ f = g.opensRange.ι := by
    simpa only [s, Category.assoc] using g.isoOpensRange_inv_comp
  have hy : f x ∈ g.opensRange := ⟨⟨x, f.mem_quasiFiniteLocus.mpr hx⟩, rfl⟩
  exact f.le_isoLocus_of_dominant_section s hs hy

/-- A morphism is quasi-finite at each point above its isomorphism locus. -/
theorem quasiFiniteAt_of_mem_isoLocus {x : X}
    (hx : f x ∈ f.isoLocus) : f.QuasiFiniteAt x := by
  let V := f.isoLocus
  let z : f ⁻¹ᵁ V := ⟨x, hx⟩
  have h : LocallyQuasiFinite ((f ⁻¹ᵁ V).ι ≫ f) :=
    (morphismRestrict_ι f V) ▸ inferInstanceAs (LocallyQuasiFinite ((f ∣_ V) ≫ V.ι))
  exact (quasiFiniteAt_comp_iff_of_isOpenImmersion (f := (f ⁻¹ᵁ V).ι) (g := f)
    (x := z)).mp (((f ⁻¹ᵁ V).ι ≫ f).quasiFiniteAt z)

section Normal

variable [IsReduced X] [IsIntegral Y] [IsNormalScheme Y] [IsModification f]

/-- A proper birational morphism to a normal integral scheme is an isomorphism over a
neighbourhood of a point exactly when the fibre contains a quasi-finite point. -/
theorem mem_isoLocus_iff_exists_quasiFiniteAt {y : Y} :
    y ∈ f.isoLocus ↔ ∃ x : X, f x = y ∧ f.QuasiFiniteAt x := by
  constructor
  · intro hy
    have : Surjective f := inferInstance
    obtain ⟨x, rfl⟩ := f.surjective y
    exact ⟨x, rfl, f.quasiFiniteAt_of_mem_isoLocus hy⟩
  · rintro ⟨x, rfl, hx⟩
    exact f.mem_isoLocus_of_quasiFiniteAt hx

/-- A finite fibre of a modification with normal integral target lies over the
isomorphism locus. -/
theorem mem_isoLocus_of_finite_preimage_singleton (y : Y) (hy : (f ⁻¹' {y}).Finite) :
    y ∈ f.isoLocus := by
  obtain ⟨x, rfl⟩ := f.surjective y
  have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr hy
  exact f.mem_isoLocus_of_quasiFiniteAt
    (quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _))

/-- Every codimension-one point of a locally Noetherian normal target belongs to the
isomorphism locus of a modification with reduced source. -/
theorem mem_isoLocus_of_coheight_eq_one [IsLocallyNoetherian Y] {y : Y} (hy : coheight y = 1) :
    y ∈ f.isoLocus := by
  have := IsNormalScheme.isDiscreteValuationRing_stalk y hy
  exact f.mem_isoLocus_of_valuationRing y

/-- On a normal locally Noetherian integral scheme of dimension at most two, the centre of a
modification with reduced source consists of closed points. -/
theorem centre_subset_closedPoints [IsLocallyNoetherian Y] (hY : topologicalKrullDim Y ≤ 2) :
    f.centre ⊆ closedPoints Y := by
  intro y hy
  have hnot : y ∉ f.isoLocus := by
    simpa only [f.centre_def, Set.mem_compl_iff, SetLike.mem_coe] using hy
  have hcodim0 : coheight y ≠ 0 := by
    intro h
    have he := Scheme.eq_genericPoint_of_isMax (coheight_eq_zero.mp h)
    obtain ⟨z, hz⟩ := (IsModification.dense_isoLocus f).nonempty
    exact hnot (he ▸ (genericPoint_specializes z).mem_open f.isoLocus.isOpen hz)
  have hcodim1 : coheight y ≠ 1 := fun h ↦ hnot (f.mem_isoLocus_of_coheight_eq_one h)
  have hle (z : Y) : coheight z ≤ 2 :=
    WithBot.coe_le_coe.mp ((TauCeti.coheight_le_topologicalKrullDim z).trans hY)
  have hy2 : 2 ≤ coheight y :=
    (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
      (lt_of_le_of_ne (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hcodim0)) hcodim1.symm)
  rw [mem_closedPoints_iff, ← closure_eq_iff_isClosed]
  refine Set.Subset.antisymm (fun z hz ↦ ?_) subset_closure
  have hzy := Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hz)
  by_contra hz'
  have hlt : z < y := lt_of_le_not_ge hzy fun hyz ↦
    hz' (((Scheme.le_iff_specializes.mp hyz).antisymm (Scheme.le_iff_specializes.mp hzy)).eq)
  have hstep := Order.coheight_add_one_le hlt
  rw [le_antisymm (hle y) hy2] at hstep
  exact (by decide : ¬ (2 : ℕ∞) + 1 ≤ 2) (hstep.trans (hle z))

/-- The centre of a proper birational morphism to a normal Noetherian integral surface is
a finite set of closed points. -/
theorem finite_centre [IsNoetherian Y] (hY : topologicalKrullDim Y ≤ 2) :
    f.centre.Finite :=
  f.isClosed_centre.finite_of_subset_closedPoints (f.centre_subset_closedPoints hY)

end Normal

/-- A modification with irreducible Noetherian source has finitely many codimension-one
points mapping into its centre. -/
theorem finite_coheight_one_preimage_centre [IrreducibleSpace X] [IsNoetherian X]
    [IsModification f] : {x ∈ f ⁻¹' f.centre | coheight x = 1}.Finite := by
  have hclosed : IsClosed (f ⁻¹' f.centre) := f.isClosed_centre.preimage f.continuous
  have : QuasiSober (f ⁻¹' f.centre) := hclosed.isClosedEmbedding_subtypeVal.quasiSober
  refine NoetherianSpace.finite_coheight_one_of_closure_ne_univ ?_
  rw [hclosed.closure_eq]
  obtain ⟨U, -, hU, hIso⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  obtain ⟨x, hx⟩ := hU.nonempty
  intro h
  have hxC : f x ∈ f.centre := by
    exact Set.mem_preimage.mp (h ▸ Set.mem_univ x)
  have hxNotIso : f x ∉ f.isoLocus := by
    simpa only [f.centre_def, Set.mem_compl_iff, SetLike.mem_coe] using hxC
  exact hxNotIso (f.le_isoLocus_iff.mpr hIso hx)

end AlgebraicGeometry.Scheme.Hom
