/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
import QPainleve.AlgebraicGeometry.Cohomology.SerreVanishing
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Twist
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction
import QPainleve.AlgebraicGeometry.LineBundle.Power
import QPainleve.AlgebraicGeometry.LineBundle.TensorProduct
import QPainleve.AlgebraicGeometry.Morphisms.Finite
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Basic
import QPainleve.AlgebraicGeometry.Scheme.Sections
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Projective morphisms collapsing exceptional curves

Twisting by an exceptional curve of the first kind lowers the degree of a line
bundle on the exceptional projective line by one at each step. The degree-zero
twist of a sufficiently ample bundle supplies a projective morphism that is
quasi-finite off the curve, as in the [Stacks Project, Section 54.16][Stacks].

[Stacks]: https://stacks.math.columbia.edu/tag/0C2I
-/

public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open LineBundleClass

variable {X : Scheme.{u}} {E : X.IdealSheafData}

/-- A positive exceptional twist changes the restriction degree by minus its exponent.
The degree is measured over the field of the exceptional projective line. -/
theorem IsEffectiveCartier.intersectionNumber_tensorPow_dual_of_degree
    (hE : E.IsEffectiveCartier) {κ : Type u} [Field κ]
    (e : projectiveLine κ ≅ E.subscheme)
    (hdeg : intersectionNumber κ (e.hom ≫ E.subschemeι)
      (LineBundleClass.mk hE.toInvertibleSheaf) = 1)
    (L : InvertibleSheaf X) (n : ℕ) :
    intersectionNumber κ (e.hom ≫ E.subschemeι)
      (LineBundleClass.mk (L.tensorProduct (hE.toInvertibleSheaf.dual.tensorPow n))) =
        intersectionNumber κ (e.hom ≫ E.subschemeι) (LineBundleClass.mk L) - n := by
  rw [mk_tensorProduct, mk_tensorPow, ← inv_mk, intersectionNumber_mul_of_isIntegral,
    intersectionNumber_pow_of_isIntegral, intersectionNumber_inv_of_isIntegral, hdeg]
  ring

private theorem subsingleton_cohomology_exceptional_quotient
    (M : InvertibleSheaf X) {κ : Type u} [Field κ] (e : projectiveLine κ ≅ E.subscheme)
    (hdeg : -1 ≤ intersectionNumber κ (e.hom ≫ E.subschemeι) (LineBundleClass.mk M)) :
    Subsingleton (Cohomology (M.obj ⊗ E.pushforwardSubscheme) 1) := by
  let i := E.subschemeι
  let N := (Scheme.Modules.pullback i).obj M.obj
  let P := (InvertibleSheaf.pullback (e.hom ≫ i)).obj M
  let d := intersectionNumber κ (e.hom ≫ i) (LineBundleClass.mk M)
  have hP : InvertibleSheaf.eulerDegree κ P = d := by
    simp only [d, P, intersectionNumber_def, pullback_mk, eulerDegree_mk]
  obtain ⟨t⟩ := (projectiveLine.nonempty_iso_twistingSheaf_iff κ P d).mpr hP
  let t' := ((Scheme.Modules.pullbackComp e.hom i).app M.obj) ≪≫
    eqToIso (InvertibleSheaf.pullback_obj_obj (e.hom ≫ i) M).symm ≪≫ t
  have := E.isIso_tensorRestrictionHom M
  let c := (cohomologyFunctor _ 1).mapIso (asIso (E.tensorRestrictionHom M)) ≪≫
    cohomologyPushforwardIso i N 1
  let c' := (cohomologyFunctor _ 1).mapIso ((e.hom.pullbackIsoPushforwardInv).app N) ≪≫
    cohomologyPushforwardIso (inv e.hom) N 1
  let b := Pi.basisFun κ (Fin 2)
  have hd : -1 ≤ d := hdeg
  have hz : Subsingleton (Cohomology (Proj.twistingSheaf
      (TauCeti.SymmetricAlgebra.homogeneousSubmodule κ (Fin 2 → κ)) d) 1) :=
    b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt (by omega : -2 < d)
      Nat.one_pos
  let h := c ≪≫ c'.symm ≪≫ (cohomologyFunctor _ 1).mapIso t'
  exact @Function.Injective.subsingleton _ _ _ h.addCommGroupIsoToAddEquiv.injective hz

/-- If first cohomology vanishes before twisting, it vanishes after each exceptional
twist whose restriction degree is at least `-1`, starting from a nonnegative
restriction degree. This is the vanishing in Stacks Project, Lemma 54.16.7(1). -/
theorem IsEffectiveCartier.subsingleton_cohomology_one_tensorPow_dual_of_le
    (hE : E.IsEffectiveCartier) {κ : Type u} [Field κ]
    (e : projectiveLine κ ≅ E.subscheme)
    (hdeg : intersectionNumber κ (e.hom ≫ E.subschemeι)
      (LineBundleClass.mk hE.toInvertibleSheaf) = 1)
    (L : InvertibleSheaf X) (hL : Subsingleton (Cohomology L.obj 1))
    (n : ℕ) (hn : (n : ℤ) ≤
      intersectionNumber κ (e.hom ≫ E.subschemeι) (LineBundleClass.mk L) + 1) :
    Subsingleton (Cohomology (L.tensorProduct (hE.toInvertibleSheaf.dual.tensorPow n)).obj 1) := by
  let M (j : ℕ) := L.tensorProduct (InvertibleSheaf.tensorPow hE.toInvertibleSheaf.dual j)
  induction n with
  | zero =>
    have h : LineBundleClass.mk (M 0) = LineBundleClass.mk L := by simp [M, mk_tensorProduct]
    let t := (cohomologyFunctor _ 1).mapIso (mk_eq_mk_iff.mp h).some
    exact @Function.Injective.subsingleton _ _ _ t.addCommGroupIsoToAddEquiv.injective hL
  | succ j ih =>
    let h := hE.tensorProductTensorPowSuccIdealIso L j
    have h₁ : Subsingleton (Cohomology ((M (j + 1)).obj ⊗ E.sheaf) 1) := by
      have hvan := ih (by omega)
      exact @Function.Injective.subsingleton _ _ _
        ((cohomologyFunctor _ 1).mapIso h).addCommGroupIsoToAddEquiv.injective hvan
    have h₂ : Subsingleton (Cohomology ((M (j + 1)).obj ⊗ E.pushforwardSubscheme) 1) := by
      apply subsingleton_cohomology_exceptional_quotient _ e
      rw [hE.intersectionNumber_tensorPow_dual_of_degree e hdeg]
      omega
    have hmid := (E.shortExact_tensor_toPushforwardSubscheme (M (j + 1)).obj)
    have hvan := subsingleton_cohomology_X₂ hmid 1 h₁ h₂
    let t := (cohomologyFunctor _ 1).mapIso (ρ_ (M (j + 1)).obj).symm
    exact @Function.Injective.subsingleton _ _ _ t.addCommGroupIsoToAddEquiv.injective hvan

private theorem exists_section_of_degree_zero
    (hE : E.IsEffectiveCartier) {κ : Type u} [Field κ] (e : projectiveLine κ ≅ E.subscheme)
    (L : InvertibleSheaf X) (n : ℕ)
    (hn : (n : ℤ) = intersectionNumber κ (e.hom ≫ E.subschemeι) (LineBundleClass.mk L))
    (hdeg : intersectionNumber κ (e.hom ≫ E.subschemeι)
      (LineBundleClass.mk hE.toInvertibleSheaf) = 1)
    (hL : Subsingleton (Cohomology L.obj 1)) (hnpos : 0 < n) :
    let M := L.tensorProduct (InvertibleSheaf.tensorPow hE.toInvertibleSheaf.dual n)
    ∃ s : Γ(M.obj, ⊤), (E.support : Set X) ⊆ M.obj.nonvanishingLocus s := by
  intro M
  let N := (InvertibleSheaf.pullback E.subschemeι).obj M
  have hzero : intersectionNumber κ (e.hom ≫ E.subschemeι) (LineBundleClass.mk M) = 0 := by
    simp only [M, hE.intersectionNumber_tensorPow_dual_of_degree e hdeg, hn, sub_self]
  have hclass : LineBundleClass.mk N = 1 := by
    apply (LineBundleClass.pullbackEquiv e).injective
    apply_fun fun a ↦ projectiveLine.picardDegreeEquiv κ (Additive.ofMul a)
    · simpa only [projectiveLine.picardDegreeEquiv_apply, toMul_ofMul,
        map_one, pullbackEquiv_apply, N, ← pullback_mk, pullback_comp,
        intersectionNumber_def, eulerDegree_one] using hzero
  obtain ⟨t⟩ := mk_eq_one_iff.mp hclass
  let t' := t.symm ≪≫ eqToIso (InvertibleSheaf.pullback_obj_obj E.subschemeι M)
  let y := t'.hom.app ⊤ (1 : Γ(E.subscheme, ⊤))
  have hy : ((Scheme.Modules.pullback E.subschemeι).obj M.obj).nonvanishingLocus y = ⊤ := by
    exact (nonvanishingLocus_hom_app t' (1 : Γ(E.subscheme, ⊤))).trans
      ((nonvanishingLocus_unit (1 : Γ(E.subscheme, ⊤))).trans (E.subscheme.basicOpen_one))
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
  have α :
      M.obj ⊗ E.sheaf ≅ (L.tensorProduct (hE.toInvertibleSheaf.dual.tensorPow (n - 1))).obj := by
    simpa only [hn', M] using hE.tensorProductTensorPowSuccIdealIso L (n - 1)
  have hvan := hE.subsingleton_cohomology_one_tensorPow_dual_of_le e hdeg L hL (n - 1)
    (by omega)
  have hvan' : Subsingleton (Cohomology (M.obj ⊗ E.sheaf) 1) :=
    @Function.Injective.subsingleton _ _ _
      ((cohomologyFunctor _ 1).mapIso α).addCommGroupIsoToAddEquiv.injective hvan
  obtain ⟨s, hs⟩ := E.surjective_pullbackSectionsLE_of_subsingleton_cohomology_one M hvan' y
  rw [← hs, nonvanishingLocus_pullbackSectionsLE, top_inf_eq, eq_top_iff] at hy
  refine ⟨s, ?_⟩
  intro x hx
  obtain ⟨z, rfl⟩ := E.range_subschemeι.symm ▸ hx
  exact hy (Opens.mem_top z)

private theorem exists_twisted_sections
    (hE : E.IsEffectiveCartier) (L : InvertibleSheaf X)
    {ι : Type u} (t : ι → Γ(L.obj, ⊤))
    (ht : ∀ i, IsAffineOpen (L.obj.nonvanishingLocus (t i))) {n : ℕ} (hn : 0 < n) :
    let M := L.tensorProduct (InvertibleSheaf.tensorPow hE.toInvertibleSheaf.dual n)
    ∃ s : ι → Γ(M.obj, ⊤), ∀ i,
      (∀ x : X, x ∈ M.obj.nonvanishingLocus (s i) ↔
          x ∈ L.obj.nonvanishingLocus (t i) ∧ x ∉ E.support) ∧
        IsAffineOpen (M.obj.nonvanishingLocus (s i)) := by
  intro M
  let D : InvertibleSheaf X := hE.toInvertibleSheaf.dual
  obtain ⟨d, hd⟩ := hE.exists_zeroIdeal_eq_dual
  have hd' : D.zeroIdeal d = E := hd
  let a := (D.tensorPowObjIso n).symm
  let b := (L.tensorProductObjIso (D.tensorPow n)).symm
  let d' := a.hom.app ⊤ (tensorPowSection d n)
  refine ⟨fun i ↦ b.hom.app ⊤ (tmulRight L.obj d' (t i)), fun i ↦ ?_⟩
  dsimp only [d']
  rw [nonvanishingLocus_hom_app, nonvanishingLocus_tmulRight,
    nonvanishingLocus_hom_app, nonvanishingLocus_tensorPowSection _ hn]
  constructor
  · intro x
    exact and_congr_right fun _ ↦ by
      exact (D.mem_nonvanishingLocus_iff_notMem_support_zeroIdeal d x).trans
        (by rw [hd'])
  · rw [← nonvanishingLocus_map (L.obj.nonvanishingLocus (t i)).leTop]
    exact (ht i).nonvanishingLocus _

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "ℙ[" R "," ι "]" => Proj (MvPolynomial.homogeneousSubmodule ι R)

private theorem exists_projective_morphism_of_cover
    {k : Type u} [Field k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    (hE : E.IsExceptionalCurveOfFirstKind)
    (M : InvertibleSheaf X) (a : Γ(M.obj, ⊤))
    (ha : (E.support : Set X) ⊆ M.obj.nonvanishingLocus a)
    {ι : Type u} (s : ι → Γ(M.obj, ⊤))
    (hcover : ∀ x : X, x ∉ E.support ↔ ∃ i, x ∈ M.obj.nonvanishingLocus (s i))
    (haffine : ∀ i, IsAffineOpen (M.obj.nonvanishingLocus (s i))) :
    ∃ (g : X ⟶ ℙ[k, Option ι]) (p : ℙ[k, Option ι]),
      g ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (Option ι) k) = X ↘ Spec (.of k) ∧
      IsProper g ∧ IsClosed ({p} : Set ℙ[k, Option ι]) ∧
      g ⁻¹' {p} = (E.support : Set X) ∧
      ∀ x, x ∉ E.support → g.QuasiFiniteAt x := by
  classical
  let v : Option ι → Γ(M.obj, ⊤) := fun i ↦ i.elim a s
  have hcov : (⨆ i, M.obj.nonvanishingLocus (v i)) = ⊤ := top_unique fun x _ ↦ by
    by_cases hx : x ∈ E.support
    · exact Opens.mem_iSup.mpr ⟨none, ha hx⟩
    · obtain ⟨i, hi⟩ := (hcover x).mp hx
      exact Opens.mem_iSup.mpr ⟨some i, hi⟩
  let f := X ↘ Spec (.of k)
  let g := M.obj.toProjectiveSpace f v hcov
  let U (i : Option ι) : ℙ[k, Option ι].Opens :=
    Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Option ι) k) (MvPolynomial.X i)
  have hg : g ≫ Proj.toSpecCoeff _ = f := M.obj.toProjectiveSpace_toSpecCoeff f v hcov
  have : IsProper (g ≫ Proj.toSpecCoeff _) := hg ▸ (Scheme.IsProjectiveOver.isProper k)
  have hproper : IsProper g := IsProper.of_comp g (Proj.toSpecCoeff _)
  have hpre (i : Option ι) : g ⁻¹ᵁ U i = M.obj.nonvanishingLocus (v i) :=
    M.obj.toProjectiveSpace_preimage_basicOpen f v hcov i
  have hU (i : Option ι) : IsAffineOpen (U i) :=
    Proj.isAffineOpen_basicOpen _ _
      ((MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X k i)) one_pos
  have hmem (i : Option ι) (x : X) : g x ∈ U i ↔ x ∈ M.obj.nonvanishingLocus (v i) := by
    rw [← Scheme.Hom.mem_preimage, hpre]
  let : IsIntegral E.subscheme := hE.isIntegral_subscheme
  let y := Classical.choice (inferInstance : Nonempty E.subscheme)
  let p := g (E.subschemeι y)
  have hsubset : Set.range (E.subschemeι ≫ g) ⊆ U none := by
    rintro _ ⟨w, rfl⟩
    exact (hmem none _).mpr (ha w.property)
  have hsingleton := (E.subschemeι ≫ g).subsingleton_range_of_isField_globalSections
    hE.isField_globalSections (hU none) hsubset
  have hp (z : E.subscheme) : g (E.subschemeι z) = p :=
    hsingleton (Set.mem_range_self z) (Set.mem_range_self y)
  have himage : g '' (E.support : Set X) = {p} := by
    rw [← E.range_subschemeι, ← Set.range_comp]
    exact Set.range_eq_singleton hp
  refine ⟨g, p, hg, hproper, himage ▸ g.isClosedMap _ E.support.isClosed, ?_, ?_⟩
  · ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · by_contra h
      obtain ⟨i, hi⟩ := (hcover x).mp h
      have he : g x = p := hx
      have hm : p ∈ U (some i) := he ▸ (hmem (some i) x).mpr hi
      exact ((hcover _).mpr ⟨i, (hmem (some i) _).mp hm⟩) y.property
    · obtain ⟨z, rfl⟩ := E.range_subschemeι.symm ▸ hx
      exact hp z
  · intro x hx
    obtain ⟨i, hi⟩ := (hcover x).mp hx
    exact g.quasiFiniteAt_of_isAffineOpen (hU (some i))
      ((hpre (some i)).symm ▸ haffine i) ((hmem (some i) x).mpr hi)

/-- On a projective scheme over a field, an exceptional curve of the first kind is the
set-theoretic fibre over a closed point of a proper morphism to a finite-dimensional
projective space. The morphism is over the base field and quasi-finite at every point
off the curve. This supplies the projective morphism used in Castelnuovo contraction. -/
theorem IsExceptionalCurveOfFirstKind.exists_projective_morphism_contracting_exceptional_curve
    (hE : E.IsExceptionalCurveOfFirstKind)
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] :
    ∃ (ι : Type u) (_ : Finite ι) (g : X ⟶ ℙ[k, ι]) (p : ℙ[k, ι]),
      g ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k) = X ↘ Spec (.of k) ∧
      IsProper g ∧ IsClosed ({p} : Set ℙ[k, ι]) ∧
      g ⁻¹' {p} = (E.support : Set X) ∧
      ∀ x, x ∉ E.support → g.QuasiFiniteAt x := by
  obtain ⟨κ, _, e, he⟩ := hE.exists_iso
  let i := e.hom ≫ E.subschemeι
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (e.hom ≫ E.subschemeι))
  let h := hE.isEffectiveCartier
  have hd : intersectionNumber κ i (LineBundleClass.mk h.toInvertibleSheaf) = 1 := by
    rw [intersectionNumber_mk]
    exact (projectiveLine.nonempty_iso_twistingSheaf_iff κ _ 1).mp he
  obtain ⟨A, hA⟩ := X.exists_isAmple_of_isProjectiveOver k
  obtain ⟨H, rfl⟩ := LineBundleClass.mk_surjective A
  obtain ⟨m, hm, hvan, ι, _, t, ht, hta⟩ :=
    (X ↘ Spec (.of k)).exists_tensorPow_affine_cover_and_subsingleton_cohomology_one H hA
  let L := H.tensorPow m
  let d := intersectionNumber κ i (LineBundleClass.mk L)
  have hdpos : 0 < d := by
    have hpos := (hA.pullback_of_isAffineHom i).eulerDegree_pos (k := κ)
    have hpos' : 0 < intersectionNumber κ i (LineBundleClass.mk H) := by
      simpa only [intersectionNumber_def] using hpos
    dsimp only [d, L]
    rw [mk_tensorPow, intersectionNumber_pow_of_isIntegral]
    exact mul_pos (Int.natCast_pos.mpr hm) hpos'
  let n := d.toNat
  have hn : (n : ℤ) = d := Int.toNat_of_nonneg hdpos.le
  have hnpos : 0 < n := by omega
  let M := L.tensorProduct (InvertibleSheaf.tensorPow h.toInvertibleSheaf.dual n)
  obtain ⟨a, ha⟩ := exists_section_of_degree_zero h e L n hn hd hvan hnpos
  obtain ⟨s, hs⟩ := exists_twisted_sections h L t hta hnpos
  have hcover (x : X) : x ∉ E.support ↔ ∃ j, x ∈ M.obj.nonvanishingLocus (s j) := by
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (ht.symm ▸ Opens.mem_top x)
      exact ⟨j, ((hs j).1 x).mpr ⟨hj, hx⟩⟩
    · rintro ⟨j, hj⟩
      exact (((hs j).1 x).mp hj).2
  exact ⟨Option ι, inferInstance,
    exists_projective_morphism_of_cover hE M a ha s hcover (fun j ↦ (hs j).2)⟩

end AlgebraicGeometry.Scheme.IdealSheafData
