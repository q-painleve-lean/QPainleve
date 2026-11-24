/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank

import QPainleve.AlgebraicGeometry.Cohomology.LineBundleLifting
import QPainleve.AlgebraicGeometry.VectorBundle.LineSubbundle
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.Algebra.Homology.ShortComplex.Splitting

/-!
# Splitting line bundle extensions on the projective line

In an extension of one line bundle by another, a maximal-degree map from a twist
into the middle term forces the quotient degree to be at most the subbundle degree.
A lift of the quotient's identity then gives the splitting. For the degree argument,
see [McKernan, Splitting type, Theorem 4.1](https://mathweb.ucsd.edu/~jmckerna/Teaching/17-18/Autumn/206A/l_4.pdf).
The rank-two case is used in the classification of ruled surfaces.
-/

public section

open CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable {k : Type u} [Field k]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
local notation "P" => projectiveLine k
local notation "𝒪(" d ")" => Proj.twistingSheaf 𝒜 d
local notation "ℒ" => fun d : ℤ ↦
  (ObjectProperty.FullSubcategory.mk (𝒪(d)) inferInstance : InvertibleSheaf P)

/-- A line bundle of degree at least `-1` on the projective line has zero first
cohomology. -/
theorem subsingleton_cohomology_one_of_eulerDegree {A : InvertibleSheaf P}
    (hd : -1 ≤ A.eulerDegree k) : Subsingleton (Cohomology A.obj 1) := by
  obtain ⟨e⟩ := (nonempty_iso_twistingSheaf_iff k A _).mpr rfl
  have hz := (Pi.basisFun k (Fin 2)).subsingleton_cohomology_twistingSheaf_of_neg_card_lt
    (by omega : -2 < A.eulerDegree k) Nat.one_pos
  exact @Function.Injective.subsingleton _ _ _
    ((cohomologyFunctor P 1).mapIso e).addCommGroupIsoToAddEquiv.injective hz

/-- Tensoring a line bundle with the dual of another subtracts their degrees. -/
@[simp]
theorem eulerDegree_tensorProduct_dual (A B : InvertibleSheaf P) :
    (InvertibleSheaf.tensorProduct A B.dual).eulerDegree k =
      A.eulerDegree k - B.eulerDegree k := by
  rw [← LineBundleClass.eulerDegree_mk, LineBundleClass.mk_tensorProduct,
    ← LineBundleClass.inv_mk,
    LineBundleClass.eulerDegree_mul k (Scheme.IsCurveOver.coheight_le_one (k := k)),
    eulerDegree_inv, LineBundleClass.eulerDegree_mk, LineBundleClass.eulerDegree_mk,
    sub_eq_add_neg]

private theorem subsingleton_cohomology_one_tensor_dual (A B : InvertibleSheaf P)
    (hd : B.eulerDegree k - A.eulerDegree k ≤ 1) :
    Subsingleton (Cohomology (A.obj ⊗ B.dual.obj) 1) := by
  let : Subsingleton (Cohomology (InvertibleSheaf.tensorProduct A B.dual).obj 1) :=
    subsingleton_cohomology_one_of_eulerDegree (by rw [eulerDegree_tensorProduct_dual]; omega)
  let e : Cohomology (InvertibleSheaf.tensorProduct A B.dual).obj 1 ≃+
      Cohomology (A.obj ⊗ B.dual.obj) 1 :=
    ((cohomologyFunctor P 1).mapIso
      (InvertibleSheaf.tensorProductObjIso A B.dual)).addCommGroupIsoToAddEquiv
  exact e.surjective.subsingleton

/-- A line bundle admits a nonzero map to any line bundle of at least the same
degree on the projective line. -/
theorem exists_hom_ne_zero_of_eulerDegree_le (A B : InvertibleSheaf P)
    (h : A.eulerDegree k ≤ B.eulerDegree k) : ∃ f : A.obj ⟶ B.obj, f ≠ 0 := by
  let d := B.eulerDegree k - A.eulerDegree k
  let F := tensorRight A.dual.obj
  have : F.IsEquivalence := by
    dsimp only [F]
    rw [← A.tensorRightDualEquivalence_functor]
    infer_instance
  let T := InvertibleSheaf.tensorProduct B A.dual
  have hd : T.eulerDegree k = d := eulerDegree_tensorProduct_dual B A
  obtain ⟨e⟩ := (nonempty_iso_twistingSheaf_iff k T d).mpr hd
  have hf : 0 < Module.finrank k (Cohomology 𝒪(d) 0) := by
    rw [finrank_cohomology_zero_twistingSheaf]
    omega
  let := Module.nontrivial_of_finrank_pos hf
  let α : Cohomology 𝒪(d) 0 ≃ (𝟙_ (projectiveLine k).Modules ⟶ 𝒪(d)) :=
    (cohomologyZeroEquiv 𝒪(d)).toEquiv.trans (𝒪(d)).unitHomEquivTop.symm
  obtain ⟨v, hv⟩ := exists_ne (α.symm 0)
  have hα : α v ≠ 0 := fun h ↦ hv (α.eq_symm_apply.mpr h)
  let e' := e.symm ≪≫ InvertibleSheaf.tensorProductObjIso B A.dual
  let g : F.obj A.obj ⟶ F.obj B.obj := (A.evaluationDualIso.hom ≫ α v) ≫ e'.hom
  have hg : g ≠ 0 := by
    intro hg
    exact hα ((comp_eq_zero_iff_of_epi A.evaluationDualIso.hom).mp
      ((comp_eq_zero_iff_of_mono e'.hom).mp hg))
  refine ⟨F.preimage g, fun heq ↦ hg ?_⟩
  let : MonoidalPreadditive (projectiveLine k).Modules :=
    TauCeti.SheafOfModules.monoidalPreadditive (projectiveLine k).sheaf
  have hz : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ by simp [F]⟩
  simpa only [Functor.map_preimage, Functor.map_zero] using congrArg F.map heq

/-- An extension of line bundles on the projective line splits if the subbundle
has degree at least the quotient degree minus one. The splitting is of the
specified exact sequence. -/
theorem nonempty_splitting_of_eulerDegree_sub_le_one
    {A B : InvertibleSheaf P} {V : (projectiveLine k).Modules}
    {i : A.obj ⟶ V} {p : V ⟶ B.obj} {w : i ≫ p = 0}
    (hS : (ShortComplex.mk i p w).ShortExact) (hd : B.eulerDegree k - A.eulerDegree k ≤ 1) :
    Nonempty (ShortComplex.mk i p w).Splitting := by
  obtain ⟨s, hs⟩ := surjective_postcomp_of_subsingleton_cohomology_tensor_dual hS B
    (subsingleton_cohomology_one_tensor_dual A B hd) (𝟙 B.obj)
  exact ⟨ShortComplex.Splitting.ofExactOfSection _ hS.exact s hs hS.mono_f⟩

/-- If the middle sheaf admits no nonzero map from any twist of degree strictly
greater than the subbundle degree, then the quotient has at most the subbundle
degree and the given sequence splits. -/
theorem eulerDegree_le_and_nonempty_splitting_of_maximal
    {A B : InvertibleSheaf P} {V : (projectiveLine k).Modules} {i : A.obj ⟶ V} {p : V ⟶ B.obj}
    {w : i ≫ p = 0} (hS : (ShortComplex.mk i p w).ShortExact)
    (hmax : ∀ n : ℤ, A.eulerDegree k < n → ∀ f : 𝒪(n) ⟶ V, f = 0) :
    B.eulerDegree k ≤ A.eulerDegree k ∧ Nonempty (ShortComplex.mk i p w).Splitting := by
  have hle : B.eulerDegree k ≤ A.eulerDegree k := by
    by_contra! hlt
    let N : InvertibleSheaf P := ℒ (A.eulerDegree k + 1)
    have hn : N.eulerDegree k = A.eulerDegree k + 1 := eulerDegree_twistingSheaf k _
    obtain ⟨g, hg⟩ := exists_hom_ne_zero_of_eulerDegree_le N B (by omega)
    obtain ⟨f, hf⟩ := surjective_postcomp_of_subsingleton_cohomology_tensor_dual hS N
      (subsingleton_cohomology_one_tensor_dual A N (by omega)) g
    have hz : f = 0 := hmax _ (by omega : A.eulerDegree k < A.eulerDegree k + 1) f
    exact hg (by simpa only [hz, zero_comp] using hf.symm)
  exact ⟨hle, nonempty_splitting_of_eulerDegree_sub_le_one hS (by omega)⟩

/-- A fiberwise nonzero maximal twist in a rank-two bundle on `ℙ¹` is a direct
summand. The other summand is a twist of at most the same degree, and the splitting
identifies the given map with the first summand inclusion. -/
theorem exists_iso_biprod_twistingSheaf_of_maximal
    (E : FiniteLocallyFreeSheaf.FixedRank P 2) {a : ℤ} (i : 𝒪(a) ⟶ E.obj.obj)
    (hi : ∀ x : P, (Scheme.Modules.pullback ((projectiveLine k).fromSpecResidueField x)).map i ≠ 0)
    (hmax : ∀ b : ℤ, a < b → ∀ f : 𝒪(b) ⟶ E.obj.obj, f = 0) :
    ∃ (b : ℤ) (e : E.obj.obj ≅ 𝒪(a) ⊞ 𝒪(b)), b ≤ a ∧ i ≫ e.hom = biprod.inl := by
  let L : InvertibleSheaf P := ℒ a
  obtain ⟨hmono, hQ⟩ := E.mono_and_isInvertible_cokernel_of_fiberwise_ne_zero L i hi
  let Q : InvertibleSheaf P := ⟨cokernel i, hQ⟩
  have ha : L.eulerDegree k = a := eulerDegree_twistingSheaf k a
  have hS : (ShortComplex.mk (X₁ := L.obj) (X₃ := Q.obj) i (cokernel.π i)
      (cokernel.condition i)).ShortExact := TauCeti.cokernelSequence_shortExact i
  obtain ⟨hdeg, ⟨s⟩⟩ := eulerDegree_le_and_nonempty_splitting_of_maximal
    (A := L) (B := Q) (i := i) (p := cokernel.π i) hS (fun b hb ↦ hmax b (ha ▸ hb))
  let b := Q.eulerDegree k
  obtain ⟨e⟩ := (nonempty_iso_twistingSheaf_iff k Q b).mpr rfl
  let t := biprod.mapIso (Iso.refl (𝒪(a))) e
  have hinl : i ≫ s.isoBinaryBiproduct.hom = biprod.inl := s.f_isoBinaryBiproduct_hom
  refine ⟨b, s.isoBinaryBiproduct ≪≫ t, hdeg.trans_eq ha, ?_⟩
  calc
    _ = (i ≫ s.isoBinaryBiproduct.hom) ≫ t.hom := (Category.assoc _ _ _).symm
    _ = biprod.inl ≫ t.hom := congrArg (· ≫ t.hom) hinl
    _ = _ := by simp only [t, biprod.mapIso_hom, Iso.refl_hom, biprod.inl_map, Category.id_comp]

end TauCeti.AlgebraicGeometry.projectiveLine
