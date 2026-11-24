/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import QPainleve.AlgebraicGeometry.LineBundle.SectionExtension
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Basic
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Basic
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Projective embeddings from ample line bundles

On a proper scheme over an affine base, an ample line bundle gives a projective
embedding. Choose a finite affine cover by nonvanishing opens, extend generators
of the affine coordinate rings by clearing denominators, and include the resulting
sections as projective coordinates.

The construction follows the affine-base argument in the
[Stacks Project, Section 29.40](https://stacks.math.columbia.edu/tag/02NO).
-/

public section

open AlgebraicGeometry CategoryTheory Filter TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

private theorem exists_affineOpen_coordinate_generators (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (κ : Type u) (_ : Finite κ) (a : κ → Γ(U.toScheme, ⊤)),
      Function.Surjective
        (MvPolynomial.eval₂Hom ((ΓSpecIso (.of R)).inv ≫ (U.ι ≫ f).appTop).hom a) := by
  let b := ((ΓSpecIso (.of R)).inv ≫ (U.ι ≫ f).appTop).hom
  have : IsAffine U.toScheme := hU
  have ht : (U.ι ≫ f).appTop.hom.FiniteType := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]
    exact (U.ι ≫ f).finiteType_appLE (isAffineOpen_top _) (isAffineOpen_top _) le_top
  have h : b.FiniteType :=
    ht.comp (.of_surjective _ (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).inv).2)
  let : Algebra R Γ(U.toScheme, ⊤) := b.toAlgebra
  let : Algebra.FiniteType R Γ(U.toScheme, ⊤) := h
  obtain ⟨κ, _, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FiniteType R Γ(U.toScheme, ⊤))
  refine ⟨κ, inferInstance, q ∘ MvPolynomial.X, fun y ↦ ?_⟩
  obtain ⟨p, rfl⟩ := hq y
  exact ⟨p, (AlgHom.congr_fun (MvPolynomial.aeval_unique q) p).symm⟩

variable {M : X.Modules} [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]

private theorem surjective_eval₂Hom_sectionRatio_of_restrict (f : X ⟶ Spec (.of R))
    {ι κ : Type u} (s : ι → Γ(M, ⊤)) (i : ι) (j : κ → ι)
    (U : X.Opens) (hU : M.nonvanishingLocus (s i) = U)
    (a : κ → Γ(U.toScheme, ⊤))
    (ha : Function.Surjective
      (MvPolynomial.eval₂Hom ((ΓSpecIso (.of R)).inv ≫ (U.ι ≫ f).appTop).hom a))
    (hs : ∀ k, M.presheaf.map U.leTop.op (s (j k)) =
      U.topIso.hom (a k) • M.presheaf.map U.leTop.op (s i)) :
    let D := M.nonvanishingLocus (s i)
    Function.Surjective (MvPolynomial.eval₂Hom
      ((ΓSpecIso (.of R)).inv ≫ (D.ι ≫ f).appTop).hom
      (fun l ↦ D.topIso.inv (M.sectionRatio (M.presheaf.map D.leTop.op (s l))
        (M.presheaf.map D.leTop.op (s i)) (by rw [M.nonvanishingLocus_map, inf_idem])))) := by
  subst U
  dsimp only
  intro y
  obtain ⟨p, rfl⟩ := ha y
  refine ⟨MvPolynomial.rename j p, ?_⟩
  rw [MvPolynomial.eval₂Hom_rename]
  apply congrArg (fun b ↦ MvPolynomial.eval₂Hom _ b p)
  funext k
  let D := M.nonvanishingLocus (s i)
  have he : D ≤ M.nonvanishingLocus (M.presheaf.map D.leTop.op (s i)) := by
    rw [M.nonvanishingLocus_map, inf_idem]
  have hratio := (M.sectionRatio_eq_iff he).mpr (hs k).symm
  rw [Function.comp_apply, hratio, Iso.hom_inv_id_apply]

private theorem exists_closedImmersion_of_affine_nonvanishing_cover
    (f : X ⟶ Spec (.of R)) [IsProper f] (L : InvertibleSheaf X)
    {ι : Type u} [Finite ι] (e : ι → Γ(L.obj, ⊤))
    (hcover : (⨆ i, L.obj.nonvanishingLocus (e i)) = ⊤)
    (hAffine : ∀ i, IsAffineOpen (L.obj.nonvanishingLocus (e i))) :
    ∃ (σ : Type u) (_ : Finite σ)
      (g : X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R)),
      IsClosedImmersion g ∧ g ≫ Proj.toSpecCoeff _ = f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let U (i : ι) := L.obj.nonvanishingLocus (e i)
  choose κ hκ a ha using fun i ↦ exists_affineOpen_coordinate_generators f (U i) (hAffine i)
  let (i : ι) : Finite (κ i) := hκ i
  have he (k : Σ i, κ i) := Modules.eventually_exists_section_mul_tensorPow L (e k.1)
    ((U k.1).topIso.hom (a k.1 k.2))
  obtain ⟨n, hn, ht⟩ := ((eventually_gt_atTop 0).and (eventually_all.mpr he)).exists
  choose t ht using ht
  let s : (ι ⊕ Σ i, κ i) → Γ(tensorPow L.obj n, ⊤) :=
    Sum.elim (fun i ↦ Modules.tensorPowSection (e i) n) t
  have hD (i : ι) : (tensorPow L.obj n).nonvanishingLocus (s (.inl i)) = U i :=
    Modules.nonvanishingLocus_tensorPowSection (e i) hn
  have hcov : (⨆ i, (tensorPow L.obj n).nonvanishingLocus (s (.inl i))) = ⊤ := by
    simpa only [hD] using hcover
  have h : (⨆ i, (tensorPow L.obj n).nonvanishingLocus (s i)) = ⊤ :=
    top_unique (hcov.ge.trans (iSup_le fun i ↦
      le_iSup (fun j ↦ (tensorPow L.obj n).nonvanishingLocus (s j)) (.inl i)))
  let g := (tensorPow L.obj n).toProjectiveSpace f s h
  have hg := (tensorPow L.obj n).toProjectiveSpace_toSpecCoeff f s h
  have : IsProper (g ≫ Proj.toSpecCoeff _) := hg.symm ▸ ‹IsProper f›
  have : IsProper g := IsProper.of_comp g (Proj.toSpecCoeff _)
  refine ⟨_, inferInstance, g, ?_, hg⟩
  apply (tensorPow L.obj n).isClosedImmersion_toProjectiveSpace_of_cover f s h
    g.isClosedMap.isClosed_range Sum.inl hcov
  intro i
  refine ⟨(hD i).symm ▸ hAffine i, ?_⟩
  refine surjective_eval₂Hom_sectionRatio_of_restrict f s (.inl i) (fun k ↦ .inr ⟨i, k⟩)
    (U i) (hD i) (a i) (ha i) fun k ↦ ?_
  simpa only [s, Sum.elim_inl, Sum.elim_inr, Modules.map_tensorPowSection] using ht ⟨i, k⟩

variable (R) [X.Over (Spec (.of R))]

/-- A proper scheme over an affine base is projective if it has an ample line bundle. -/
theorem IsProjectiveOver.of_isProper_of_isAmple [IsProper (X ↘ Spec (.of R))]
    {A : LineBundleClass X} (hA : A.IsAmple) : X.IsProjectiveOver R := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective A
  obtain ⟨n, -, S, hS, h⟩ := hA.exists_finset_isAffineOpen_nonvanishingLocus_tensorPow
  choose hAffine e he using fun i : S ↦ h i i.property
  have hcover : (⨆ i, (L.tensorPow n).obj.nonvanishingLocus (e i)) = ⊤ := by
    simp_rw [he]
    exact (sSup_eq_iSup' (S : Set X.Opens)).symm.trans hS
  obtain ⟨σ, _, g, _, hg⟩ := exists_closedImmersion_of_affine_nonvanishing_cover
    (X ↘ Spec (.of R)) (L.tensorPow n) e hcover (fun i ↦ (he i).symm ▸ hAffine i)
  have : g.IsOver (Spec (.of R)) := ⟨hg⟩
  exact IsProjectiveOver.of_isClosedImmersion R g

/-- A scheme finite over a projective scheme over an affine base is projective over that base. -/
theorem IsProjectiveOver.of_isFinite {Y : Scheme.{u}} [Y.Over (Spec (.of R))]
    [Y.IsProjectiveOver R] (f : X ⟶ Y) [IsFinite f] [f.IsOver (Spec (.of R))] :
    X.IsProjectiveOver R := by
  have : IsProper (X ↘ Spec (.of R)) := comp_over f (Spec (.of R)) ▸
    inferInstanceAs (IsProper (f ≫ (Y ↘ Spec (.of R))))
  obtain ⟨A, hA⟩ := Y.exists_isAmple_of_isProjectiveOver R
  exact .of_isProper_of_isAmple R (hA.pullback_of_isAffineHom f)

end AlgebraicGeometry.Scheme
