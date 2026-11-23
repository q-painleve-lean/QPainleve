/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.RationalMap
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Embedding
public import QPainleve.AlgebraicGeometry.RationalMap.ClosedImmersion
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import QPainleve.AlgebraicGeometry.CartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.Modules.Pullback.Sections
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Domain
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Extension
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Pullback
import QPainleve.AlgebraicGeometry.RationalMap.Composition
import TauCeti.AlgebraicGeometry.Morphisms.Separated

/-!
# Resolving rational maps by principalizing their base ideals

After dominant pullback to an integral scheme, a projective section presentation
extends to a morphism exactly when the pulled-back base ideal is effective Cartier.
For a rational map into a closed subscheme of projective space, the extension lands
in that subscheme. This connects principalization of a linear system to resolution
of the rational map it presents. For the application to resolving maps of surfaces,
see [Stacks Project, Lemma 54.4.3](https://stacks.math.columbia.edu/tag/0C5H).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X Y Z : Scheme.{u}} {R ι : Type u} [CommRing R]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule ι R
local notation "ℙ" => Proj 𝒜

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

/-- The pullback of the base ideal of a projective section presentation is effective Cartier
exactly when the precomposed rational map has a unique morphism representing it over the base. -/
theorem isEffectiveCartier_comap_iSup_zeroIdeal_iff_existsUnique_projective_morphism
    [IsIntegral X] [Nonempty Y]
    (L : InvertibleSheaf Y) (f : Y ⟶ Spec (.of R)) (s : ι → Γ(L.obj, ⊤))
    (i : ι) (hi : Dense (L.obj.nonvanishingLocus (s i) : Set Y))
    (g : X ⟶ Y) [IsDominant g] :
    ((⨆ j, L.zeroIdeal (s j)).comap g).IsEffectiveCartier ↔
      ∃! h : X ⟶ ℙ, h ≫ Proj.toSpecCoeff 𝒜 = g ≫ f ∧
        h.toRationalMap = g.toRationalMap.comp
          (L.obj.partialMapToProjectiveSpace f s i hi).toRationalMap := by
  let M := (pullback g).obj L
  let t (j : ι) := g.pullbackSectionsLE L.obj ⊤ ⊤ (Eq.ge (g.preimage_top)) (s j)
  have hd : Dense (M.obj.nonvanishingLocus (t i) : Set X) :=
    L.obj.dense_nonvanishingLocus_pullbackSectionsLE_top g hi
  have he : (M.obj.partialMapToProjectiveSpace (g ≫ f) t i hd).toRationalMap =
      g.toRationalMap.comp (L.obj.partialMapToProjectiveSpace f s i hi).toRationalMap :=
    L.obj.toRationalMap_partialMapToProjectiveSpace_pullback f s g i hi
  have hI : (⨆ j, M.zeroIdeal (t j)) = (⨆ j, L.zeroIdeal (s j)).comap g := by
    simpa only [t, Scheme.Hom.pullbackSectionsLE_top] using
      L.iSup_zeroIdeal_pullbackSections g s
  rw [← hI, ← he]
  refine ⟨M.exists_projective_morphism_of_cartier_base_ideal (g ≫ f) t i hd, ?_⟩
  rintro ⟨h, ⟨-, hh⟩, -⟩
  apply M.isEffectiveCartier_iSup_zeroIdeal_of_domain_eq_top (g ≫ f) t hd
  rw [← hh]
  exact top_unique h.toPartialMap.le_domain_toRationalMap

/-- For a morphism resolving a projective section presentation, the inverse image of the
base ideal is Cartier. The resolved hyperplane class is the pullback of the original
line class times the class of that ideal. -/
theorem pullback_twistingSheafOne_eq_of_resolving
    [IsIntegral X] [Nonempty Y]
    (L : InvertibleSheaf Y) (f : Y ⟶ Spec (.of R)) (s : ι → Γ(L.obj, ⊤))
    (i : ι) (hi : Dense (L.obj.nonvanishingLocus (s i) : Set Y))
    (g : X ⟶ Y) [IsDominant g] (h : X ⟶ ℙ)
    (hover : h ≫ Proj.toSpecCoeff 𝒜 = g ≫ f)
    (hrep : h.toRationalMap = g.toRationalMap.comp
      (L.obj.partialMapToProjectiveSpace f s i hi).toRationalMap) :
    ∃ hI : ((⨆ j, L.zeroIdeal (s j)).comap g).IsEffectiveCartier,
      LineBundleClass.pullback h
          (LineBundleClass.mk (⟨Proj.twistingSheaf 𝒜 1, inferInstance⟩ : InvertibleSheaf ℙ)) =
        LineBundleClass.pullback g (LineBundleClass.mk L) *
          LineBundleClass.mk hI.toInvertibleSheaf := by
  let : (ℙ).IsSeparated := Scheme.IsSeparated.of_isSeparated (Proj.toSpecCoeff 𝒜)
  have hI := (L.isEffectiveCartier_comap_iSup_zeroIdeal_iff_existsUnique_projective_morphism
    f s i hi g).mpr ⟨h, ⟨hover, hrep⟩, fun h' hh' ↦
      Scheme.Hom.toRationalMap_injective (hh'.2.trans hrep.symm)⟩
  let M := (pullback g).obj L
  let t (j : ι) := g.pullbackSectionsLE L.obj ⊤ ⊤ g.preimage_top.ge (s j)
  have hsum : (⨆ j, M.zeroIdeal (t j)) = (⨆ j, L.zeroIdeal (s j)).comap g := by
    simpa only [t, Scheme.Hom.pullbackSectionsLE_top] using
      L.iSup_zeroIdeal_pullbackSections g s
  have hIt : (⨆ j, M.zeroIdeal (t j)).IsEffectiveCartier := hsum.symm ▸ hI
  have hd : Dense (M.obj.nonvanishingLocus (t i) : Set X) :=
    L.obj.dense_nonvanishingLocus_pullbackSectionsLE_top g hi
  have hr : h.toRationalMap = (M.obj.partialMapToProjectiveSpace (g ≫ f) t i hd).toRationalMap :=
    hrep.trans (L.obj.toRationalMap_partialMapToProjectiveSpace_pullback f s g i hi).symm
  obtain ⟨e, -⟩ := M.exists_iso_pullbackTwistingSheaf_of_cartier_base_ideal (g ≫ f) t i hd hIt h hr
  refine ⟨hI, ?_⟩
  rw [LineBundleClass.pullback_mk, LineBundleClass.pullback_mk, mul_comm,
    ← LineBundleClass.mk_toInvertibleSheaf_congr hIt hI hsum, ← LineBundleClass.mk_tensorProduct]
  exact LineBundleClass.mk_eq_mk_iff.mpr ⟨e⟩

end TauCeti.AlgebraicGeometry.InvertibleSheaf

namespace AlgebraicGeometry.Scheme.RationalMap

/-- A dominant morphism from an integral scheme resolves a rational map into a closed
subscheme of projective space exactly when it makes the base ideal of the chosen presentation
effective Cartier. The resolving morphism is unique and preserves the base morphism. -/
theorem isEffectiveCartier_comap_iSup_zeroIdeal_iff_existsUnique_hom_comp
    [IsIntegral X] [Nonempty Y] (q : Y ⤏ Z)
    (f : Y ⟶ Spec (.of R)) (e : Z ⟶ ℙ) [IsClosedImmersion e]
    (L : InvertibleSheaf Y) (s : ι → Γ(L.obj, ⊤))
    (i : ι) (hi : Dense (L.obj.nonvanishingLocus (s i) : Set Y))
    (hq : (L.obj.partialMapToProjectiveSpace f s i hi).toRationalMap = q.compHom e)
    (g : X ⟶ Y) [IsDominant g] :
    ((⨆ j, L.zeroIdeal (s j)).comap g).IsEffectiveCartier ↔
      ∃! h : X ⟶ Z, h ≫ e ≫ Proj.toSpecCoeff 𝒜 = g ≫ f ∧
        h.toRationalMap = g.toRationalMap.comp q := by
  rw [L.isEffectiveCartier_comap_iSup_zeroIdeal_iff_existsUnique_projective_morphism f s i hi g,
    hq, comp_compHom]
  let r := g.toRationalMap.comp q
  constructor
  · rintro ⟨v, ⟨hv, hvq⟩, hv_unique⟩
    obtain ⟨h, ⟨he, hh⟩, hh_unique⟩ :=
      r.existsUnique_hom_of_toRationalMap_eq_compHom e v hvq
    refine ⟨h, ⟨by rw [← Category.assoc, he, hv], hh⟩, fun h' hh' ↦ ?_⟩
    refine hh_unique h' ⟨hv_unique (h' ≫ e) ⟨?_, ?_⟩, hh'.2⟩
    · exact (Category.assoc _ _ _).trans hh'.1
    · rw [← Hom.toRationalMap_compHom, hh'.2]
  · rintro ⟨h, ⟨hh, hq'⟩, hh_unique⟩
    refine ⟨h ≫ e, ⟨by rwa [Category.assoc], ?_⟩, fun v hv ↦ ?_⟩
    · rw [← Hom.toRationalMap_compHom, hq']
    · obtain ⟨h', ⟨he, hr⟩, -⟩ :=
        r.existsUnique_hom_of_toRationalMap_eq_compHom e v hv.2
      have hh' : h' = h := hh_unique h' ⟨by rw [← Category.assoc, he, hv.1], hr⟩
      rw [← he, hh']

/-- A rational map to a projective scheme admits a finite family of sections with
at least one nonzero member whose base ideal detects resolution. After any dominant morphism
from an integral scheme, the map extends uniquely over the base exactly when the pulled-back
ideal defines an effective Cartier divisor. -/
theorem exists_section_family_for_resolution
    [IsIntegral Y] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [Z.Over (Spec (.of R))] [Z.IsProjectiveOver R]
    (q : Y ⤏ Z) (f : Y ⟶ Spec (.of R)) [q.IsOver f (Z ↘ Spec (.of R))]
    {A : LineBundleClass Y} (hA : A.IsAmple) :
    ∃ (ι : Type u) (_ : Finite ι) (L : InvertibleSheaf Y) (s : ι → Γ(L.obj, ⊤)),
      (∃ i, s i ≠ 0) ∧
      ∀ {W : Scheme.{u}} [IsIntegral W] (g : W ⟶ Y) [IsDominant g],
        ((⨆ j, L.zeroIdeal (s j)).comap g).IsEffectiveCartier ↔
          ∃! h : W ⟶ Z, h ≫ (Z ↘ Spec (.of R)) = g ≫ f ∧
            h.toRationalMap = g.toRationalMap.comp q := by
  obtain ⟨ι, hfin, e, he, he'⟩ := Z.exists_isClosedImmersion_polynomial_of_isProjectiveOver R
  have : (q.compHom e).IsOver f (Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule ι R)) :=
    RationalMap.IsOver.compHom inferInstance he'
  obtain ⟨L, s, i, hi, hq⟩ := (q.compHom e).exists_projective_section_presentation f hA
  refine ⟨ι, hfin, L, s, ⟨i, ?_⟩, ?_⟩
  · intro h
    rw [h, Scheme.Modules.nonvanishingLocus_zero] at hi
    exact hi.nonempty.ne_empty rfl
  · intro W _ g _
    simpa only [he'] using
      q.isEffectiveCartier_comap_iSup_zeroIdeal_iff_existsUnique_hom_comp f e L s i hi hq g

end AlgebraicGeometry.Scheme.RationalMap
