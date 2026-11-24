/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import QPainleve.AlgebraicGeometry.Cohomology.SerreVanishing
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.GlobalGeneration
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Fiber
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Pullback
import QPainleve.AlgebraicGeometry.Curves.Degree.Ample
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.GlobalGeneration
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Twist
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction
import QPainleve.AlgebraicGeometry.Morphisms.Finite
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Cohomology
import QPainleve.AlgebraicGeometry.Scheme.Sections
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Projective morphisms collapsing exceptional curves

Twisting by an exceptional curve of the first kind lowers the degree of a line
bundle on the exceptional projective line by one at each step. The degree-zero
twist of a sufficiently ample bundle supplies a projective morphism that is
quasi-finite off the curve, as in the [Stacks Project, Section 54.16][Stacks].
Sections of the degree-one twist lift from the curve and make it the scheme-theoretic
fibre over the collapsed point.

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
      apply subsingleton_cohomology_one_tensor_pushforwardSubscheme_of_projectiveLine _ e
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

private theorem exists_twist_sections_covering_exceptional
    (hE : E.IsEffectiveCartier) (hcompact : IsCompact (E.support : Set X))
    {κ : Type u} [Field κ] (e : projectiveLine κ ≅ E.subscheme)
    (L : InvertibleSheaf X) (n : ℕ) (hn : 2 ≤ n)
    (hdeg : intersectionNumber κ (e.hom ≫ E.subschemeι)
      (LineBundleClass.mk hE.toInvertibleSheaf) = 1)
    (hL : Subsingleton (Cohomology L.obj 1))
    (hd : (n : ℤ) = intersectionNumber κ (e.hom ≫ E.subschemeι) (LineBundleClass.mk L)) :
    let M := L.tensorProduct (hE.toInvertibleSheaf.dual.tensorPow n)
    let N := hE.toInvertibleSheaf.tensorProduct M
    ∃ (ι : Type u) (_ : Finite ι) (t : ι → Γ(N.obj, ⊤)),
      ∀ x ∈ E.support, ∃ j, x ∈ N.obj.nonvanishingLocus (t j) := by
  classical
  intro M N
  let A (j : ℕ) := L.tensorProduct (hE.toInvertibleSheaf.dual.tensorPow j)
  have hn₁ : n - 1 + 1 = n := by omega
  have hn₂ : n - 2 + 1 = n - 1 := by omega
  let α : N.obj ≅ (A (n - 1)).obj := (M.idealTwistIso hE) ≪≫
    β_ E.sheaf M.obj ≪≫ (by simpa only [hn₁, M, A] using
      hE.tensorProductTensorPowSuccIdealIso L (n - 1))
  let β : N.obj ⊗ E.sheaf ≅ (A (n - 2)).obj :=
    whiskerRightIso α E.sheaf ≪≫ (by simpa only [hn₂, A] using
      hE.tensorProductTensorPowSuccIdealIso L (n - 2))
  have hv := hE.subsingleton_cohomology_one_tensorPow_dual_of_le e hdeg L hL (n - 2) (by omega)
  have hvan : Subsingleton (Cohomology (N.obj ⊗ E.sheaf) 1) :=
    @Function.Injective.subsingleton _ _ _
      ((cohomologyFunctor _ 1).mapIso β).addCommGroupIsoToAddEquiv.injective hv
  let P := (InvertibleSheaf.pullback E.subschemeι).obj N
  have hQ : 0 ≤ ((InvertibleSheaf.pullback e.hom).obj P).eulerDegree κ := by
    dsimp only [P]
    rw [← eulerDegree_mk, ← pullback_mk, ← pullback_mk, pullback_comp,
      ← intersectionNumber_def, (mk_eq_mk_iff).mpr ⟨α⟩]
    dsimp only [A]
    rw [hE.intersectionNumber_tensorPow_dual_of_degree e hdeg, ← hd]
    omega
  have hP := P.isGloballyGenerated_of_nonneg_eulerDegree_projectiveLine e hQ
  let U (t : Γ(N.obj, ⊤)) := N.obj.nonvanishingLocus t
  have hc : (E.support : Set X) ⊆ ⋃ t, (U t : Set X) := by
    intro x hx
    obtain ⟨y, rfl⟩ := E.range_subschemeι.ge hx
    obtain ⟨s, hs⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp hP y
    let d : P.obj ≅ (Scheme.Modules.pullback E.subschemeι).obj N.obj :=
      eqToIso (InvertibleSheaf.pullback_obj_obj E.subschemeι N)
    have hs' : y ∈ ((Scheme.Modules.pullback E.subschemeι).obj N.obj).nonvanishingLocus
        (d.hom.app ⊤ s) := by
      rw [nonvanishingLocus_hom_app d s]
      exact hs
    obtain ⟨t, ht⟩ := E.surjective_pullbackSectionsLE_of_subsingleton_cohomology_one N hvan
      (d.hom.app ⊤ s)
    rw [← ht, nonvanishingLocus_pullbackSectionsLE, top_inf_eq] at hs'
    exact Set.mem_iUnion.mpr ⟨t, E.subschemeι.mem_preimage.mp hs'⟩
  obtain ⟨S, hS⟩ := hcompact.elim_finite_subcover
    (fun t ↦ (U t : Set X)) (fun t ↦ (U t).isOpen) hc
  refine ⟨S, inferInstance, Subtype.val, ?_⟩
  intro x hx
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hS hx)
  obtain ⟨hmem, hxt⟩ := Set.mem_iUnion.mp ht
  exact ⟨⟨t, hmem⟩, hxt⟩

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "ℙ[" R "," ι "]" => Proj (MvPolynomial.homogeneousSubmodule ι R)

private theorem IsExceptionalCurveOfFirstKind.exists_closed_image_point_of_isAffineOpen
    (hE : E.IsExceptionalCurveOfFirstKind) {Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g]
    {U : Y.Opens} (hU : IsAffineOpen U) (hmem : ∀ z : E.subscheme, g (E.subschemeι z) ∈ U) :
    ∃ y : E.subscheme, IsClosed ({g (E.subschemeι y)} : Set Y) ∧
      ∀ z : E.subscheme, g (E.subschemeι z) = g (E.subschemeι y) := by
  have := hE.isIntegral_subscheme
  let y := Classical.choice (inferInstance : Nonempty E.subscheme)
  have hsubset : Set.range (E.subschemeι ≫ g) ⊆ U := by
    rintro _ ⟨w, rfl⟩
    exact hmem w
  have hsingleton := (E.subschemeι ≫ g).subsingleton_range_of_isField_globalSections
    hE.isField_globalSections hU hsubset
  have hy (z : E.subscheme) : g (E.subschemeι z) = g (E.subschemeι y) :=
    hsingleton (Set.mem_range_self z) (Set.mem_range_self y)
  have himage : g '' (E.support : Set X) = {g (E.subschemeι y)} := by
    rw [← E.range_subschemeι, ← Set.range_comp]
    exact Set.range_eq_singleton hy
  exact ⟨y, himage ▸ g.isClosedMap _ E.support.isClosed, hy⟩

private theorem exists_projective_morphism_of_cover
    {k : Type u} [Field k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    (hE : E.IsExceptionalCurveOfFirstKind)
    (M : InvertibleSheaf X) (a : Γ(M.obj, ⊤))
    (ha : (E.support : Set X) ⊆ M.obj.nonvanishingLocus a)
    {ι : Type u} (s : ι → Γ(M.obj, ⊤))
    (hcover : ∀ x : X, x ∉ E.support ↔ ∃ i, x ∈ M.obj.nonvanishingLocus (s i))
    (haffine : ∀ i, IsAffineOpen (M.obj.nonvanishingLocus (s i)))
    {ι' : Type u} (t : ι' → Γ((hE.isEffectiveCartier.toInvertibleSheaf.tensorProduct M).obj, ⊤))
    (ht : ∀ x ∈ E.support, ∃ i, x ∈
      (hE.isEffectiveCartier.toInvertibleSheaf.tensorProduct M).obj.nonvanishingLocus (t i)) :
    ∃ (g : X ⟶ ℙ[k,Option (ι ⊕ ι')]) (p : ℙ[k,Option (ι ⊕ ι')]),
      g ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (Option (ι ⊕ ι')) k) =
        X ↘ Spec (.of k) ∧
      IsProper g ∧ IsClosed ({p} : Set ℙ[k,Option (ι ⊕ ι')]) ∧
      g ⁻¹' {p} = (E.support : Set X) ∧
      (IsIntegral X →
        ((ℙ[k,Option (ι ⊕ ι')]).fromSpecResidueField p).ker.comap g = E) ∧
      ∀ x, x ∉ E.support → g.QuasiFiniteAt x := by
  classical
  let v : Option (ι ⊕ ι') → Γ(M.obj, ⊤) :=
    fun i ↦ i.elim a
      (Sum.elim s (fun j ↦ (M.idealTwistInclusion hE.isEffectiveCartier).app ⊤ (t j)))
  have hcov : (⨆ i, M.obj.nonvanishingLocus (v i)) = ⊤ := top_unique fun x _ ↦ by
    by_cases hx : x ∈ E.support
    · exact Opens.mem_iSup.mpr ⟨none, ha hx⟩
    · obtain ⟨i, hi⟩ := (hcover x).mp hx
      exact Opens.mem_iSup.mpr ⟨some (.inl i), hi⟩
  let f := X ↘ Spec (.of k)
  let g := M.obj.toProjectiveSpace f v hcov
  let U (i : Option (ι ⊕ ι')) : ℙ[k,Option (ι ⊕ ι')].Opens :=
    Proj.basicOpen _ (MvPolynomial.X i)
  have hg : g ≫ Proj.toSpecCoeff _ = f := M.obj.toProjectiveSpace_toSpecCoeff f v hcov
  have : IsProper (g ≫ Proj.toSpecCoeff _) := hg ▸ (Scheme.IsProjectiveOver.isProper k)
  have hproper : IsProper g := IsProper.of_comp g (Proj.toSpecCoeff _)
  have hpre (i : Option (ι ⊕ ι')) : g ⁻¹ᵁ U i = M.obj.nonvanishingLocus (v i) :=
    M.obj.toProjectiveSpace_preimage_basicOpen f v hcov i
  have hU (i : Option (ι ⊕ ι')) : IsAffineOpen (U i) :=
    Proj.isAffineOpen_basicOpen _ _
      ((MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X k i)) one_pos
  have hmem (i : Option (ι ⊕ ι')) (x : X) : g x ∈ U i ↔ x ∈ M.obj.nonvanishingLocus (v i) := by
    rw [← Scheme.Hom.mem_preimage, hpre]
  have := hE.isIntegral_subscheme
  obtain ⟨y, hclosed, hp⟩ := hE.exists_closed_image_point_of_isAffineOpen g (hU none)
    (fun w ↦ (hmem none _).mpr (ha w.property))
  let p := g (E.subschemeι y)
  have hfiber : g ⁻¹' {p} = (E.support : Set X) := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · by_contra h
      obtain ⟨i, hi⟩ := (hcover x).mp h
      have he : g x = p := hx
      have hm : p ∈ U (some (.inl i)) := he ▸ (hmem (some (.inl i)) x).mpr hi
      exact ((hcover _).mpr ⟨i, (hmem (some (.inl i)) _).mp hm⟩) y.property
    · obtain ⟨z, rfl⟩ := E.range_subschemeι.symm ▸ hx
      exact hp z
  refine ⟨g, p, hg, hproper, hclosed, hfiber, ?_, ?_⟩
  · intro hI
    exact hE.isEffectiveCartier.comap_ker_of_projective_sections M f v hcov t
      (fun j ↦ some (.inr j)) (fun _ ↦ rfl) ht p hclosed hfiber ⟨E.subschemeι y, y.property⟩
  · intro x hx
    obtain ⟨i, hi⟩ := (hcover x).mp hx
    exact g.quasiFiniteAt_of_isAffineOpen (hU (some (.inl i)))
      ((hpre (some (.inl i))).symm ▸ haffine i) ((hmem (some (.inl i)) x).mpr hi)

private theorem exists_projective_morphism_contracting_exceptional_curve_aux
    (hE : E.IsExceptionalCurveOfFirstKind)
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] :
    ∃ (ι : Type u) (_ : Finite ι) (g : X ⟶ ℙ[k,ι]) (p : ℙ[k,ι]),
      g ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k) = X ↘ Spec (.of k) ∧
      IsProper g ∧ IsClosed ({p} : Set ℙ[k,ι]) ∧
      g ⁻¹' {p} = (E.support : Set X) ∧
      (IsIntegral X → ((ℙ[k,ι]).fromSpecResidueField p).ker.comap g = E) ∧
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
  let H₂ := H.tensorPow 2
  have hH₂ : (LineBundleClass.mk H₂).IsAmple := by
    dsimp only [H₂]
    rw [mk_tensorPow]
    exact hA.pow (by decide)
  obtain ⟨m, hm, hvan, ι, _, t, ht, hta⟩ :=
    (X ↘ Spec (.of k)).exists_tensorPow_affine_cover_and_subsingleton_cohomology_one H₂ hH₂
  let L := H₂.tensorPow m
  let d := intersectionNumber κ i (LineBundleClass.mk L)
  have hd₂ : 2 ≤ d := by
    have hpos := (hA.pullback_of_isAffineHom i).eulerDegree_pos (k := κ)
    have hpos' : 0 < intersectionNumber κ i (LineBundleClass.mk H) := by
      simpa only [intersectionNumber_def] using hpos
    dsimp only [d, L, H₂]
    rw [mk_tensorPow, mk_tensorPow, ← pow_mul, intersectionNumber_pow_of_isIntegral]
    push_cast
    have hm' : 0 < (m : ℤ) := Int.natCast_pos.mpr hm
    nlinarith
  let n := d.toNat
  have hn : (n : ℤ) = d := Int.toNat_of_nonneg (by omega)
  have hnpos : 0 < n := by omega
  let M := L.tensorProduct (InvertibleSheaf.tensorPow h.toInvertibleSheaf.dual n)
  obtain ⟨a, ha⟩ := exists_section_of_degree_zero h e L n hn hd hvan hnpos
  obtain ⟨s, hs⟩ := h.exists_twisted_sections L t hta hnpos
  have hcover (x : X) : x ∉ E.support ↔ ∃ j, x ∈ M.obj.nonvanishingLocus (s j) := by
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (ht.symm ▸ Opens.mem_top x)
      exact ⟨j, ((hs j).1 x).mpr ⟨hj, hx⟩⟩
    · rintro ⟨j, hj⟩
      exact (((hs j).1 x).mp hj).2
  have : CompactSpace X := hA.compactSpace
  obtain ⟨ι', _, t', ht'⟩ := exists_twist_sections_covering_exceptional h
    E.support.isClosed.isCompact e L n (by omega) hd hvan hn
  exact ⟨Option (ι ⊕ ι'), inferInstance,
    exists_projective_morphism_of_cover hE M a ha s hcover (fun j ↦ (hs j).2) t' ht'⟩

/-- On a projective scheme over a field, an exceptional curve of the first kind is the
set-theoretic fibre over a closed point of a proper morphism to a finite-dimensional
projective space. The morphism is over the base field and quasi-finite at every point
off the curve. This supplies the projective morphism used in Castelnuovo contraction. -/
theorem IsExceptionalCurveOfFirstKind.exists_projective_morphism_contracting_exceptional_curve
    (hE : E.IsExceptionalCurveOfFirstKind)
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] :
    ∃ (ι : Type u) (_ : Finite ι) (g : X ⟶ ℙ[k,ι]) (p : ℙ[k,ι]),
      g ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k) = X ↘ Spec (.of k) ∧
      IsProper g ∧ IsClosed ({p} : Set ℙ[k,ι]) ∧
      g ⁻¹' {p} = (E.support : Set X) ∧
      ∀ x, x ∉ E.support → g.QuasiFiniteAt x := by
  obtain ⟨ι, hι, g, p, hg, hproper, hp, hpre, -, hq⟩ :=
    exists_projective_morphism_contracting_exceptional_curve_aux hE k
  exact ⟨ι, hι, g, p, hg, hproper, hp, hpre, hq⟩

/-- On an integral projective scheme over a field, the projective morphism contracting
an exceptional curve of the first kind can be chosen with that curve as its
scheme-theoretic fibre over the collapsed point. -/
theorem IsExceptionalCurveOfFirstKind.exists_projective_morphism_with_exceptional_fiber
    [IsIntegral X] (hE : E.IsExceptionalCurveOfFirstKind)
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k] :
    ∃ (ι : Type u) (_ : Finite ι) (g : X ⟶ ℙ[k,ι]) (p : ℙ[k,ι]),
      g ≫ Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι k) = X ↘ Spec (.of k) ∧
      IsProper g ∧ IsClosed ({p} : Set ℙ[k,ι]) ∧
      g ⁻¹' {p} = (E.support : Set X) ∧
      ((ℙ[k,ι]).fromSpecResidueField p).ker.comap g = E ∧
      ∀ x, x ∉ E.support → g.QuasiFiniteAt x := by
  obtain ⟨ι, hι, g, p, hg, hproper, hp, hpre, hE', hq⟩ :=
    exists_projective_morphism_contracting_exceptional_curve_aux hE k
  exact ⟨ι, hι, g, p, hg, hproper, hp, hpre, hE' inferInstance, hq⟩

end AlgebraicGeometry.Scheme.IdealSheafData
