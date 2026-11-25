/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle.Basic

import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.Basis.Prod
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra.DisjointSections
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# Splitting a projective bundle along two disjoint quotient sections

Two disjoint line-quotient sections of a rank-two projective bundle identify
the bundle with the direct sum of the quotient line bundles. The induced
projective isomorphism identifies the given sections with the two summand
quotient sections. We use the projective bundle convention of
[Stacks, Section 27.21][stacks-01OA].

[stacks-01OA]: https://stacks.math.columbia.edu/tag/01OA
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

variable {X : Scheme.{u}} (E : FixedRank X 2) (L₁ L₂ : FixedRank X 1)

local notation "F[" E "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent X) (ObjectProperty.FullSubcategory.obj E)
local notation "A[" F "]" =>
  ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra X) F)
local notation "Π[" q "]" => SymmetricAlgebra.gradedMap _ q
local notation "valid[" q "," h "]" =>
  SymmetricAlgebra.irrelevant_le_map_gradedMap_of_surjective q h
local notation "incl" =>
  (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Scheme.ringCatSheaf X)) :
    QuasicoherentSheaf X ⥤ X.Modules)
local notation "under[" q "]" => CategoryTheory.Functor.map incl q
local notation "sec[" U "," q "]" =>
  ModuleCat.Hom.hom (CategoryTheory.Functor.map
    (Scheme.Modules.sectionsFunctor (Scheme.AffineZariskiSite.toOpens U))
    under[q])

private theorem disjoint_range_affine_quotient_maps {F : QuasicoherentSheaf X}
    (q₁ : F ⟶ F[L₁]) (q₂ : F ⟶ F[L₂]) [Epi q₁.hom] [Epi q₂.hom]
    (hd : Disjoint (Set.range (L₁.relativeProjSectionOfQuotient q₁))
      (Set.range (L₂.relativeProjSectionOfQuotient q₂))) (U : X.AffineZariskiSite)
    (h₁ : Function.Surjective sec[U,q₁]) (h₂ : Function.Surjective sec[U,q₂]) :
    Disjoint (Set.range (Proj.map Π[sec[U,q₁]] valid[sec[U,q₁],h₁]))
      (Set.range (Proj.map Π[sec[U,q₂]] valid[sec[U,q₂],h₂])) := by
  let j := (F.projSymmetricAlgebraSectionsIso U).hom ≫ A[F].relativeProjCover.f U
  have hmem (L : FixedRank X 1) (q : F ⟶ F[L]) [Epi q.hom]
      (h : Function.Surjective sec[U,q]) (x : Proj _) :
      j (Proj.map Π[sec[U,q]] valid[sec[U,q],h] x) ∈
        Set.range (L.relativeProjSectionOfQuotient q) := by
    refine ⟨((F[L].projSymmetricAlgebraSectionsIso U).hom ≫ A[F[L]].relativeProjCover.f U ≫
      A[F[L]].relativeProjToBase) x, ?_⟩
    have hcomp := L.projSymmetricAlgebraSectionsIso_hom_comp_relativeProjSectionOfQuotient
      q U valid[sec[U,q],h]
    exact (congrArg (fun f : Proj _ ⟶ A[F].relativeProj ↦ f x) hcomp).symm
  rw [Set.disjoint_left]
  rintro _ ⟨x₁, rfl⟩ ⟨x₂, hx⟩
  exact Set.disjoint_left.mp hd (hmem L₁ q₁ h₁ x₁) (hx ▸ hmem L₂ q₂ h₂ x₂)

private theorem bijective_prod_sections_of_disjoint
    (q₁ : F[E] ⟶ F[L₁]) (q₂ : F[E] ⟶ F[L₂]) [Epi q₁.hom] [Epi q₂.hom]
    (hd : Disjoint (Set.range (L₁.relativeProjSectionOfQuotient q₁))
      (Set.range (L₂.relativeProjSectionOfQuotient q₂))) (U : X.AffineZariskiSite)
    (b : Module.Basis (ULift.{u} (Fin 2)) Γ(X, U.toOpens)
      ((Scheme.Modules.sectionsFunctor U.toOpens).obj E.obj.obj))
    (b₁ : Module.Basis (ULift.{u} (Fin 1)) Γ(X, U.toOpens)
      ((Scheme.Modules.sectionsFunctor U.toOpens).obj L₁.obj.obj))
    (b₂ : Module.Basis (ULift.{u} (Fin 1)) Γ(X, U.toOpens)
      ((Scheme.Modules.sectionsFunctor U.toOpens).obj L₂.obj.obj)) :
    Function.Bijective (sec[U,q₁].prod sec[U,q₂]) := by
  let R := Γ(X, U.toOpens)
  let e₁ := b₁.equiv (Module.Basis.singleton (ULift.{u} (Fin 1)) R) (Equiv.refl _)
  let e₂ := b₂.equiv (Module.Basis.singleton (ULift.{u} (Fin 1)) R) (Equiv.refl _)
  let f₁ := sec[U,q₁]
  let f₂ := sec[U,q₂]
  have hq₁ : @Epi X.Modules _ E.obj.obj L₁.obj.obj under[q₁] := ‹Epi q₁.hom›
  have hq₂ : @Epi X.Modules _ E.obj.obj L₂.obj.obj under[q₂] := ‹Epi q₂.hom›
  have h₁ : Function.Surjective f₁ :=
    @Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen X E.obj.obj L₁.obj.obj
      under[q₁] hq₁ inferInstance inferInstance U.toOpens U.property
  have h₂ : Function.Surjective f₂ :=
    @Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen X E.obj.obj L₂.obj.obj
      under[q₂] hq₂ inferInstance inferInstance U.toOpens U.property
  have hs := SymmetricAlgebra.surjective_prod_of_disjoint_projectiveSpectrum e₁ e₂
    f₁ f₂ h₁ h₂ (disjoint_range_affine_quotient_maps L₁ L₂ q₁ q₂ hd U h₁ h₂)
  let d := b₁.prod b₂
  have := Module.Finite.of_basis d
  let e := b.equiv d (Fintype.equivOfCardEq (by simp))
  exact OrzechProperty.bijective_of_surjective_of_injective e.toLinearMap _ e.injective hs

private theorem isIso_app_biprod_lift
    (q₁ : F[E] ⟶ F[L₁]) (q₂ : F[E] ⟶ F[L₂]) (U : X.AffineZariskiSite)
    (hb : Function.Bijective (sec[U,q₁].prod sec[U,q₂])) :
    let f₁ : E.obj.obj ⟶ L₁.obj.obj := under[q₁]
    let f₂ : E.obj.obj ⟶ L₂.obj.obj := under[q₂]
    IsIso (Scheme.Modules.Hom.app (biprod.lift f₁ f₂) U.toOpens) := by
  intro f₁ f₂
  let S := Scheme.Modules.sectionsFunctor U.toOpens
  let e := S.mapBiprod L₁.obj.obj L₂.obj.obj ≪≫ ModuleCat.biprodIsoProd _ _
  have h :
      S.map (biprod.lift f₁ f₂) ≫ e.hom =
        ModuleCat.ofHom (sec[U,q₁].prod sec[U,q₂]) := by
    rw [Iso.trans_hom, ← Category.assoc,
      biprod.map_lift_mapBiprod S L₁.obj.obj L₂.obj.obj f₁ f₂]
    apply (cancel_mono (ModuleCat.biprodIsoProd _ _).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply biprod.hom_ext
    · simp only [biprod.lift_fst, Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst]
      exact ModuleCat.hom_ext rfl
    · simp only [biprod.lift_snd, Category.assoc, ModuleCat.biprodIsoProd_inv_comp_snd]
      exact ModuleCat.hom_ext rfl
  have : IsIso (ModuleCat.ofHom (sec[U,q₁].prod sec[U,q₂])) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have : IsIso (S.map (biprod.lift f₁ f₂) ≫ e.hom) := h ▸ inferInstance
  have : IsIso (S.map (biprod.lift f₁ f₂)) := IsIso.of_isIso_comp_right _ e.hom
  exact Functor.map_isIso (forget₂ (ModuleCat Γ(X, U.toOpens)) AddCommGrpCat)
    (S.map (biprod.lift f₁ f₂))

/-- Two line quotients of a rank-two bundle whose sections have disjoint images
induce an isomorphism to the direct sum of the quotient bundles. -/
theorem isIso_biprod_lift_of_disjoint_quotient_sections
    (q₁ : F[E] ⟶ F[L₁]) (q₂ : F[E] ⟶ F[L₂]) [Epi q₁.hom] [Epi q₂.hom]
    (hd : Disjoint (Set.range (L₁.relativeProjSectionOfQuotient q₁))
      (Set.range (L₂.relativeProjSectionOfQuotient q₂))) :
    IsIso (biprod.lift q₁ q₂) := by
  let rank : Option Bool → ℕ
    | none => 2
    | some _ => 1
  let bundle : (i : Option Bool) → FixedRank X (rank i)
    | none => E
    | some false => L₁
    | some true => L₂
  let I := {U : X.AffineZariskiSite // ∀ i, Nonempty
    (Module.Basis (ULift.{u} (Fin (rank i))) Γ(X, U.toOpens)
      ((Scheme.Modules.sectionsFunctor U.toOpens).obj (bundle i).obj.obj))}
  let B (U : I) := U.val.toOpens
  have hB : TopologicalSpace.Opens.IsBasis (Set.range B) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro W x hx
    obtain ⟨U, hU, hxU, hUW, hb⟩ :=
      exists_isAffineOpen_basis_sections_family_le bundle hx
    exact ⟨U, ⟨⟨⟨U, hU⟩, hb⟩, rfl⟩, hxU, hUW⟩
  let f₁ : E.obj.obj ⟶ L₁.obj.obj := under[q₁]
  let f₂ : E.obj.obj ⟶ L₂.obj.obj := under[q₂]
  have hi : IsIso (biprod.lift f₁ f₂) :=
    Scheme.Modules.Hom.isIso_of_isBasis _ hB fun U ↦
      isIso_app_biprod_lift E L₁ L₂ q₁ q₂ U.val
        (bijective_prod_sections_of_disjoint E L₁ L₂ q₁ q₂ hd U.val
          (U.property none).some (U.property (some false)).some (U.property (some true)).some)
  let Fι := incl
  let : Fι.Additive := ⟨rfl⟩
  let e := Fι.mapBiprod F[L₁] F[L₂]
  have h := biprod.map_lift_mapBiprod Fι F[L₁] F[L₂] q₁ q₂
  have : IsIso (Fι.map (biprod.lift q₁ q₂) ≫ e.hom) := h ▸ hi
  have : IsIso (Fι.map (biprod.lift q₁ q₂)) := IsIso.of_isIso_comp_right _ e.hom
  exact isIso_of_reflects_iso _ Fι

/-- Two disjoint line-quotient sections of a rank-two projective bundle are
the images of the summand quotient sections under an isomorphism over the base. -/
theorem exists_relativeProj_iso_biprod_of_disjoint_quotient_sections
    (q₁ : F[E] ⟶ F[L₁]) (q₂ : F[E] ⟶ F[L₂]) [Epi q₁.hom] [Epi q₂.hom]
    (hd : Disjoint (Set.range (L₁.relativeProjSectionOfQuotient q₁))
      (Set.range (L₂.relativeProjSectionOfQuotient q₂))) :
    let p₁ : F[L₁] ⊞ F[L₂] ⟶ F[L₁] := biprod.fst
    let p₂ : F[L₁] ⊞ F[L₂] ⟶ F[L₂] := biprod.snd
    let : Epi p₁.hom := inferInstanceAs (Epi under[(biprod.fst : F[L₁] ⊞ F[L₂] ⟶ F[L₁])])
    let : Epi p₂.hom := inferInstanceAs (Epi under[(biprod.snd : F[L₁] ⊞ F[L₂] ⟶ F[L₂])])
    ∃ e : A[F[L₁] ⊞ F[L₂]].relativeProj ≅ A[F[E]].relativeProj,
      e.hom ≫ A[F[E]].relativeProjToBase = A[F[L₁] ⊞ F[L₂]].relativeProjToBase ∧
      L₁.relativeProjSectionOfQuotient p₁ ≫ e.hom = L₁.relativeProjSectionOfQuotient q₁ ∧
      L₂.relativeProjSectionOfQuotient p₂ ≫ e.hom = L₂.relativeProjSectionOfQuotient q₂ := by
  intro p₁ p₂ hp₁ hp₂
  let := hp₁
  let := hp₂
  have := E.isIso_biprod_lift_of_disjoint_quotient_sections L₁ L₂ q₁ q₂ hd
  let e := asIso (biprod.lift q₁ q₂)
  let eAlg : A[F[E]] ≅ A[F[L₁] ⊞ F[L₂]] :=
    (ObjectProperty.ι _).mapIso ((gradedSymmetricAlgebra X).mapIso e)
  refine ⟨CommMon.relativeProjMapIso eAlg,
    CommMon.relativeProjMapIso_hom_relativeProjToBase eAlg, ?_, ?_⟩
  · have h : e.hom ≫ p₁ = q₁ := biprod.lift_fst ..
    simpa only [h] using L₁.relativeProjSectionOfQuotient_comp_relativeProjMapIso e p₁
  · have h : e.hom ≫ p₂ = q₂ := biprod.lift_snd ..
    simpa only [h] using L₂.relativeProjSectionOfQuotient_comp_relativeProjMapIso e p₂

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
