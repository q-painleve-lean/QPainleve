/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.Quotient
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IntersectionNumber.ClosedPoint
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.SymmetricAlgebra
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.GlobalGeneration
import QPainleve.AlgebraicGeometry.VectorBundle.SectionZeroLocus
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf
import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Instances
import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.GlobalGeneration
import TauCeti.AlgebraicGeometry.Scheme.ClosedPoint
import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Bidual
import TauCeti.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Maps from twisting sheaves to vector bundles on the projective line

A nonzero vector bundle on the projective line admits a nonzero map from a line
bundle of maximal degree. Serre global generation applied to the bundle supplies
a map, and applied to its dual it gives an upper bound on the degree of its source.
The resulting section of the twisted bundle is nonzero on each residue-field fiber.
A zero in a closed fiber would factor the dual section through the ideal of that point
and hence give a map from a higher twist.

The maximal-degree argument is used in the splitting theorem on the projective line,
which enters the [classification of minimal rational surfaces][Vakil].

[Vakil]: https://math.stanford.edu/~vakil/02-245/sclass17A.pdf#page=4
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData
open scoped Topology

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

variable (k : Type u)

local notation "P" => projectiveLine k
local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
local notation "𝒪(" n ")" => Proj.twistingSheaf 𝒜 n
local notation "L(" n ")" => Proj.symmetricAlgebraTwistingBundle k (Fin 2 → k) n
local notation "tensorIso" =>
  Proj.twistingSheaf.tensorObjIso (coord k) (coord_mem k) (iSup_basicOpen_coord_eq_top k)

local instance [CommRing k] : MonoidalPreadditive (P).Modules :=
  TauCeti.SheafOfModules.monoidalPreadditive (P).sheaf

local instance [CommRing k] (a : ℤ) : (tensorRight (𝒪(a))).IsEquivalence := by
  rw [← Proj.symmetricAlgebraTwistingBundle_obj,
    ← InvertibleSheaf.tensorRightDualEquivalence_inverse]
  infer_instance

section CommRing

variable [CommRing k]

/-- A higher-degree twist has only the zero morphism to a lower-degree twist. -/
theorem hom_twistingSheaf_eq_zero_of_lt {a b : ℤ} (h : b < a)
    (f : 𝒪(a) ⟶ 𝒪(b)) : f = 0 := by
  let F := tensorRight (𝒪(-a))
  let e : (𝒪(a) ⊗ 𝒪(-a)) ≅ 𝟙_ (P).Modules :=
    tensorIso a (-a) ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫ (Proj.unitIsoTwistingSheafZero 𝒜).symm
  have hzero : Subsingleton (Scheme.Modules.Cohomology (𝒪(b + -a)) 0) :=
    SymmetricAlgebra.subsingleton_cohomology_zero_twistingSheaf_of_neg
      (by omega) (Pi.basisFun k (Fin 2))
  let : Subsingleton (𝟙_ (P).Modules ⟶ 𝒪(b + -a)) :=
    ((𝒪(b + -a)).unitHomEquivTop.trans
      (Scheme.Modules.cohomologyZeroEquiv _).symm.toEquiv).subsingleton
  have hz : e.inv ≫ F.map f ≫ (tensorIso b (-a)).hom = 0 := Subsingleton.elim _ _
  rw [comp_eq_zero_iff_of_epi, comp_eq_zero_iff_of_mono] at hz
  exact (Functor.map_eq_zero_iff F).mp hz

end CommRing

variable [Field k]

open FiniteLocallyFreeSheaf in
private theorem exists_twisting_hom_upper_bound (E : FiniteLocallyFreeSheaf P) :
    ∃ b : ℤ, ∀ a : ℤ, (∃ f : 𝒪(a) ⟶ E.obj, f ≠ 0) → a ≤ b := by
  let Edual : FiniteLocallyFreeSheaf P := dual E
  have : Edual.obj.IsFinitePresentation := Edual.property.2
  obtain ⟨n, σ, -⟩ := (Proj.eventually_exists_generatingSections_tensor_twistingSheaf
    (coord k) (coord_mem k) (iSup_basicOpen_coord_eq_top k) Edual.obj).exists
  refine ⟨n, fun a ⟨f, hf⟩ ↦ le_of_not_gt fun h ↦ hf ?_⟩
  let D := (InvertibleSheaf.toFiniteLocallyFree P).obj (L(a))
  let f' : D ⟶ E := ObjectProperty.homMk f
  let F := tensorRight (𝒪(n))
  let G := (dualEquiv (X := P)).inverse
  let g : F.obj Edual.obj ⟶ F.obj (dual D).obj := F.map (G.map f'.op).hom
  have hD : (dual D).obj = (L(a)).dual.obj :=
    (dual_obj D).trans (InvertibleSheaf.dual_obj (L(a))).symm
  obtain ⟨d⟩ : Nonempty ((L(a)).dual.obj ≅ 𝒪(-a)) := by
    apply (nonempty_iso_twistingSheaf_iff k (L(a)).dual (-a)).mpr
    rw [← LineBundleClass.eulerDegree_mk, ← LineBundleClass.inv_mk, eulerDegree_inv,
      LineBundleClass.eulerDegree_mk]
    exact congrArg Neg.neg (eulerDegree_twistingSheaf k a)
  let e := F.mapIso (eqToIso hD ≪≫ d) ≪≫ tensorIso (-a) n
  let U : (P).Modules := SheafOfModules.free σ.I
  let q : U ⟶ F.obj Edual.obj := σ.π
  have : Epi q := σ.epi
  have hπ : q ≫ g ≫ e.hom = 0 := by
    apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan σ.I)
    intro j
    let z : 𝒪(0) ≅ 𝟙_ (P).Modules := (Proj.unitIsoTwistingSheafZero 𝒜).symm
    let ι : 𝟙_ (P).Modules ⟶ U :=
      (SheafOfModules.freeCofan σ.I).inj j
    have ht : z.hom ≫ ι ≫ q ≫ g ≫ e.hom = 0 :=
      hom_twistingSheaf_eq_zero_of_lt k (by omega) _
    exact ((comp_eq_zero_iff_of_epi z.hom).mp ht).trans (comp_zero (f := ι)).symm
  have hg : g = 0 := by
    rwa [comp_eq_zero_iff_of_epi, comp_eq_zero_iff_of_mono] at hπ
  have hd := (Functor.map_eq_zero_iff F).mp hg
  have hz : G.map f'.op = 0 := ObjectProperty.hom_ext _ hd
  have hf' := (Functor.map_eq_zero_iff G).mp hz
  exact congrArg (fun (v : D ⟶ E) ↦ v.hom) (Quiver.Hom.op_inj (hf'.trans (op_zero ..).symm))

open FiniteLocallyFreeSheaf in
private theorem exists_nonzero_twisting_hom_of_imageIdealSheaf_ne_top
    (E : FiniteLocallyFreeSheaf P)
    (φ : (dual E).obj ⟶ 𝟙_ (P).Modules) (hφ : φ ≠ 0)
    (hI : φ.imageIdealSheaf ≠ ⊤) :
    ∃ (d : ℤ) (f : 𝒪(d) ⟶ E.obj), 0 < d ∧ f ≠ 0 := by
  let I := φ.imageIdealSheaf
  have hn : (I.support : Set P).Nonempty := by
    by_contra! h
    exact hI ((support_eq_bot_iff _).mp (TopologicalSpace.Closeds.coe_eq_empty.mp h))
  obtain ⟨p, hp, hclosed⟩ := I.support.isClosed.exists_closed_singleton hn
  let J := ((P).fromSpecResidueField p).ker
  have : TauCeti.AlgebraicGeometry.IsRegular P := ⟨fun _ ↦ inferInstance⟩
  have hJ : J.IsEffectiveCartier :=
    (P).isEffectiveCartier_ker_fromSpecResidueField_of_dim_eq_one hclosed
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)
  have hIJ : I ≤ J := (le_ker_fromSpecResidueField_iff_mem_support _ hclosed).mpr hp
  let Q := (InvertibleSheaf.toFiniteLocallyFree P).obj hJ.toInvertibleSheaf
  let eJ : Q.obj ≅ J.sheaf := eqToIso hJ.toInvertibleSheaf_obj
  let g : dual E ⟶ Q :=
    ObjectProperty.homMk (φ.toImageIdealSheaf ≫ sheafHomOfLE hIJ ≫ eJ.inv)
  have hg : g ≠ 0 := by
    intro hz
    have hz' : g.hom = 0 := congrArg (fun (v : dual E ⟶ Q) ↦ v.hom) hz
    let j : J.sheaf ⟶ 𝟙_ (P).Modules := J.sheafι
    have he : g.hom ≫ eJ.hom ≫ j = φ := by
      simp only [g, ObjectProperty.homMk_hom, Category.assoc, Iso.inv_hom_id_assoc]
      rw [show sheafHomOfLE hIJ ≫ j = I.sheafι from sheafHomOfLE_sheafι hIJ]
      exact φ.toImageIdealSheaf_ι
    exact hφ (he.symm.trans (hz' ▸ zero_comp))
  let G := (dualEquiv (X := P)).inverse
  let d := ((P) ↘ Spec (CommRingCat.of k)).residueDegree p
  have hd : 0 < d := Nat.pos_of_ne_zero (Scheme.Hom.residueDegree_ne_zero_of_isClosed _ hclosed)
  have hdeg : InvertibleSheaf.eulerDegree k hJ.toInvertibleSheaf.dual = d := by
    rw [← LineBundleClass.eulerDegree_mk, ← LineBundleClass.inv_mk, eulerDegree_inv,
      LineBundleClass.eulerDegree_mk_ker_fromSpecResidueField hclosed, neg_neg]
  obtain ⟨e⟩ := (nonempty_iso_twistingSheaf_iff k hJ.toInvertibleSheaf.dual d).mpr hdeg
  have hQ : (dual Q).obj = hJ.toInvertibleSheaf.dual.obj :=
    (dual_obj Q).trans (InvertibleSheaf.dual_obj _).symm
  let q : 𝒪(d) ≅ (dual Q).obj := e.symm ≪≫ eqToIso hQ.symm
  let eE : (dual (dual E)).obj ≅ E.obj :=
    (Scheme.Modules.isFiniteLocallyFree P).ι.mapIso (evalIso E).symm
  have : Mono eE.hom := mono_of_mono_fac eE.hom_inv_id
  refine ⟨d, q.hom ≫ (G.map g.op).hom ≫ eE.hom, by exact_mod_cast hd, ?_⟩
  intro hz
  have hzero : (G.map g.op).hom = 0 :=
    (comp_eq_zero_iff_of_mono eE.hom).mp ((comp_eq_zero_iff_of_epi q.hom).mp hz)
  have hmap : G.map g.op = 0 := ObjectProperty.hom_ext _ hzero
  exact hg (Quiver.Hom.op_inj (((Functor.map_eq_zero_iff G).mp hmap).trans (op_zero ..).symm))

private theorem pullback_section_ne_zero_of_twisting_hom_eq_zero
    (E : FiniteLocallyFreeSheaf P) (s : 𝟙_ (P).Modules ⟶ E.obj) (hs : s ≠ 0)
    (hmax : ∀ d : ℤ, 0 < d → ∀ f : 𝒪(d) ⟶ E.obj, f = 0) (p : P) :
    (Scheme.Modules.pullbackObjUnitIso ((P).fromSpecResidueField p)).inv ≫
      (Scheme.Modules.pullback ((P).fromSpecResidueField p)).map s ≠ 0 := by
  intro h
  let e := Scheme.Modules.dualHomUnitEquiv E.obj
  have hφ : e.symm s ≠ 0 := by
    intro hz
    apply hs
    rw [← e.apply_symm_apply s, hz, Scheme.Modules.dualHomUnitEquiv_zero]
  have hp := (E.mem_support_imageIdealSheaf_evaluation_iff s p).mpr h
  have hI : (e.symm s).imageIdealSheaf ≠ ⊤ := by
    intro he
    simp only [e, he, support_top, TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false] at hp
  obtain ⟨d, f, hd, hf⟩ := exists_nonzero_twisting_hom_of_imageIdealSheaf_ne_top k E _ hφ hI
  exact hf (hmax d hd f)

/-- A nonzero morphism from a twist of maximal degree is nonzero in every residue-field
fiber. In particular it defines a line in each fiber of the target vector bundle. -/
theorem pullback_twisting_hom_ne_zero_of_maximal (E : FiniteLocallyFreeSheaf P)
    {a : ℤ} (f : 𝒪(a) ⟶ E.obj) (hf : f ≠ 0)
    (hmax : ∀ b : ℤ, a < b → ∀ g : 𝒪(b) ⟶ E.obj, g = 0) (p : P) :
    (Scheme.Modules.pullback ((P).fromSpecResidueField p)).map f ≠ 0 := by
  let F := tensorRight (𝒪(-a))
  let e : F.obj (𝒪(a)) ≅ 𝟙_ (P).Modules :=
    tensorIso a (-a) ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫ (Proj.unitIsoTwistingSheafZero 𝒜).symm
  let s : 𝟙_ (P).Modules ⟶ F.obj E.obj := e.inv ≫ F.map f
  have hs : s ≠ 0 := fun h ↦ hf ((Functor.map_eq_zero_iff F).mp
    ((comp_eq_zero_iff_of_epi e.inv).mp h))
  let M : FiniteLocallyFreeSheaf P := E ⊗ (InvertibleSheaf.toFiniteLocallyFree P).obj (L(-a))
  have hM (d : ℤ) (hd : 0 < d) (t : 𝒪(d) ⟶ M.obj) : t = 0 := by
    let e' : F.obj (𝒪(d + a)) ≅ 𝒪(d) :=
      tensorIso (d + a) (-a) ≪≫ eqToIso (by rw [add_assoc, add_neg_cancel, add_zero])
    obtain ⟨g, hg⟩ := F.map_surjective (e'.hom ≫ t)
    exact (comp_eq_zero_iff_of_epi e'.hom).mp
      (hg.symm.trans ((congrArg F.map (hmax (d + a) (by omega) g)).trans (F.map_zero ..)))
  let i := (P).fromSpecResidueField p
  let G := Scheme.Modules.pullback i
  have : MonoidalPreadditive (Spec ((P).residueField p)).Modules :=
    TauCeti.SheafOfModules.monoidalPreadditive (Spec ((P).residueField p)).sheaf
  let c := Scheme.Modules.pullbackTensorRightIso i (𝒪(-a))
  intro hp
  have h : G.map (F.map f) ≫ (c.app E.obj).hom =
      (c.app (𝒪(a))).hom ≫ (tensorRight (G.obj (𝒪(-a)))).map (G.map f) :=
    c.hom.naturality f
  have hp' : G.map f = 0 := hp
  rw [hp', Functor.map_zero, comp_zero] at h
  have hz := (comp_eq_zero_iff_of_mono ((c.app E.obj).hom)).mp h
  have hzero : G.map s = 0 := (G.map_comp e.inv (F.map f)).trans (hz ▸ comp_zero)
  exact pullback_section_ne_zero_of_twisting_hom_eq_zero k M s hs hM p (hzero ▸ comp_zero)

/-- A nonzero vector bundle on the projective line admits a nonzero morphism from a twist
of maximal degree. The morphism is nonzero on every residue-field fiber. -/
theorem exists_maximal_twisting_hom (E : FiniteLocallyFreeSheaf P) (hE : ¬ IsZero E.obj) :
    ∃ (a : ℤ) (f : 𝒪(a) ⟶ E.obj), f ≠ 0 ∧
      (∀ b : ℤ, a < b → ∀ g : 𝒪(b) ⟶ E.obj, g = 0) ∧
      ∀ p : P, (Scheme.Modules.pullback ((P).fromSpecResidueField p)).map f ≠ 0 := by
  obtain ⟨a, ⟨f, hf⟩, hmax⟩ := Int.exists_greatest_of_bdd (exists_twisting_hom_upper_bound k E)
    (exists_nonzero_twisting_hom k E.obj hE)
  have hzero (b : ℤ) (hb : a < b) (g : 𝒪(b) ⟶ E.obj) : g = 0 := by
    by_contra hg
    exact (not_le_of_gt hb) (hmax b ⟨g, hg⟩)
  exact ⟨a, f, hf, hzero, pullback_twisting_hom_ne_zero_of_maximal k E f hf hzero⟩

end TauCeti.AlgebraicGeometry.projectiveLine
