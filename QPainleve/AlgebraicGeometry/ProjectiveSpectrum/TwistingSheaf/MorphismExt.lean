/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Sections

import QPainleve.AlgebraicGeometry.Modules.Pullback.Generator
import QPainleve.RingTheory.GradedAlgebra.HomogeneousLocalization.DegreeOne

/-!
# Extensionality of projective morphisms using the first twist

For a graded algebra generated in degree one, a morphism to its projective
spectrum is determined by the images of the degree-one forms in its pullback
of the first twisting sheaf. This holds scheme-theoretically, including for a
nonreduced source. On a standard chart the ratios of those forms recover the
pullback of regular functions. See [Stacks, Lemma 27.16.11][stacks].

[stacks]: https://stacks.math.columbia.edu/tag/01O4
-/

public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry.Scheme.Modules
open HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Proj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {Y : Scheme.{u}}

local notation "L" => twistingSheaf 𝒜 1
local notation "t[" U "," a "]" => toTwistingSheaf 𝒜 (Nat.cast_one : ((1 : ℕ) : ℤ) = 1) U a

variable {g h : Y ⟶ Proj 𝒜}

/-- Any two points of a projective spectrum generated in degree one lie on a
common degree-one standard chart. -/
theorem exists_mem_basicOpen_degreeOne_pair
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤) (x y : Proj 𝒜) :
    ∃ r : 𝒜 1, x ∈ basicOpen 𝒜 r ∧ y ∈ basicOpen 𝒜 r := by
  let B (r : 𝒜 1) := basicOpen 𝒜 r
  have hB (x : Proj 𝒜) : ∃ r : 𝒜 1, x ∈ B r :=
    Opens.mem_iSup.mp ((iSup_basicOpen_eq_top_of_adjoin_eq_top 𝒜 hgen).ge (Set.mem_univ x))
  obtain ⟨r, hr⟩ := hB x
  obtain ⟨s, hs⟩ := hB y
  by_cases hr' : y ∈ B r
  · exact ⟨r, hr, hr'⟩
  by_cases hs' : x ∈ B s
  · exact ⟨s, hs', hs⟩
  refine ⟨r + s, ?_, ?_⟩
  · intro hrs
    have hs₀ : (s : A) ∈ (x).asHomogeneousIdeal.toIdeal := of_not_not hs'
    have hsum : (r : A) + s ∈ (x).asHomogeneousIdeal.toIdeal := hrs
    have hmem := sub_mem hsum hs₀
    rw [add_sub_cancel_right] at hmem
    exact hr hmem
  · intro hrs
    have hr₀ : (r : A) ∈ (y).asHomogeneousIdeal.toIdeal := of_not_not hr'
    have hsum : (r : A) + s ∈ (y).asHomogeneousIdeal.toIdeal := hrs
    have hmem := sub_mem hsum hr₀
    rw [add_sub_cancel_left] at hmem
    exact hs hmem

private theorem resLE_eq_of_pullback_toTwistingSheaf
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤)
    (e : (pullback g).obj L ≅ (pullback h).obj L) {V : Y.Opens} (hV : IsAffineOpen V)
    (r : 𝒜 1) (hg : V ≤ g ⁻¹ᵁ basicOpen 𝒜 r) (hh : V ≤ h ⁻¹ᵁ basicOpen 𝒜 r)
    (hloc : ∀ a : 𝒜 1, let D := basicOpen 𝒜 r
      e.hom.app V (g.pullbackSectionsLE L D V hg t[D, a]) =
        h.pullbackSectionsLE L D V hh t[D, a]) :
    g.resLE (basicOpen 𝒜 r) V hg = h.resLE (basicOpen 𝒜 r) V hh := by
  let D := basicOpen 𝒜 r
  have hD : IsAffineOpen D := isAffineOpen_basicOpen _ _ r.property Nat.one_pos
  have hr : t[D, r] = twistingSheaf.chartGenerator 1 (r : A) r.property D le_rfl :=
    toTwistingSheaf_one_eq_chartGenerator r D le_rfl
  let t := twistingSheaf.chartSectionsLinearEquiv 1 (r : A) r.property D le_rfl
  have ht : (fun b : Γ(Proj 𝒜, D) ↦ b • t[D, r]) = t := by
    funext b
    rw [hr]
    exact (twistingSheaf.chartSectionsLinearEquiv_apply 1 r.val r.property D le_rfl b).symm
  have hcanc := (g.bijective_smul_pullbackSectionsLE hD hV hg
    (s := t[D, r]) (ht.symm ▸ t.bijective)).1
  have happ : g.appLE D V hg = h.appLE D V hh := by
    let k := awayToSection 𝒜 (r : A)
    let : IsIso k := (basicOpenIsoAway 𝒜 (r : A) r.property Nat.one_pos).isIso_hom
    apply (cancel_epi k).mp
    apply CommRingCat.hom_ext
    apply Away.ringHom_ext_of_degreeOne r.property hgen
    intro a
    have hre : t[D, a] = k (Away.dehomogenize r.property a) • t[D, r] := by
      rw [Away.dehomogenize_apply_of_mem r.property a.property,
        hr]
      exact twistingSheaf.toTwistingSheaf_eq_smul_chartGenerator 1 a r.property
    have hc₁ :
        e.hom.app V (g.pullbackSectionsLE L D V hg t[D, a]) =
          h.pullbackSectionsLE L D V hh t[D, a] := hloc a
    rw [hre, (g.pullbackSectionsLE L D V hg).map_smulₛₗ,
      (h.pullbackSectionsLE L D V hh).map_smulₛₗ] at hc₁
    apply hcanc
    have hi : Function.LeftInverse (e.inv.app V) (e.hom.app V) := fun s ↦
      congrArg (fun m : (pullback g).obj L ⟶ (pullback g).obj L ↦ m.app V s) e.hom_inv_id
    apply hi.injective
    exact hc₁.trans (by rw [Scheme.Modules.Hom.app_smul, hloc r]; rfl)
  apply (cancel_mono hD.isoSpec.hom).mp
  rw [IsAffineOpen.isoSpec_hom, ← Scheme.Opens.toSpecΓ_SpecMap_appLE,
    ← Scheme.Opens.toSpecΓ_SpecMap_appLE, happ]

/-- Pulling back the degree-one forms to the same line bundle determines a morphism
to the projective spectrum of an algebra generated in degree one. -/
theorem hom_ext_of_pullback_toTwistingSheaf
    (hgen : Algebra.adjoin (𝒜 0) (𝒜 1 : Set A) = ⊤)
    (e : (pullback g).obj L ≅ (pullback h).obj L)
    (he : ∀ a : 𝒜 1, e.hom.app ⊤ (g.pullbackSectionsLE L ⊤ ⊤ g.preimage_top.ge t[⊤, a]) =
      h.pullbackSectionsLE L ⊤ ⊤ h.preimage_top.ge t[⊤, a]) : g = h := by
  let B (r : 𝒜 1) := basicOpen 𝒜 r
  let W := {W : Y.Opens // IsAffineOpen W ∧ ∃ r : 𝒜 1,
    W ≤ g ⁻¹ᵁ B r ∧ W ≤ h ⁻¹ᵁ B r}
  let U (w : W) := w.val
  have hcover : IsOpenCover U := by
    refine IsOpenCover.mk (eq_top_iff.mpr fun y _ ↦ ?_)
    obtain ⟨r, hgr, hhr⟩ := exists_mem_basicOpen_degreeOne_pair hgen (g y) (h y)
    let O := g ⁻¹ᵁ B r ⊓ h ⁻¹ᵁ B r
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hle⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ O from ⟨hgr, hhr⟩) O.isOpen
    exact Opens.mem_iSup.mpr ⟨⟨V, hV, r, hle.trans inf_le_left, hle.trans inf_le_right⟩, hyV⟩
  refine (Y.openCoverOfIsOpenCover U hcover).hom_ext _ _ fun w ↦ ?_
  obtain ⟨r, hg, hh⟩ := w.property.2
  let V := w.val
  let D := B r
  have hloc (a : 𝒜 1) :
      e.hom.app V (g.pullbackSectionsLE L D V hg t[D, a]) =
        h.pullbackSectionsLE L D V hh t[D, a] := by
    rw [← res_toTwistingSheaf (V := D) (i := homOfLE le_top) (h := Nat.cast_one) (r := a)]
    rw [g.pullbackSectionsLE_map _ ⊤ V (le_trans le_top g.preimage_top.ge) _ hg,
      h.pullbackSectionsLE_map _ ⊤ V (le_trans le_top h.preimage_top.ge) _ hh]
    rw [← g.presheaf_map_pullbackSectionsLE L ⊤ ⊤ g.preimage_top.ge (homOfLE le_top),
      ← h.presheaf_map_pullbackSectionsLE L ⊤ ⊤ h.preimage_top.ge (homOfLE le_top)]
    exact (e.hom.mapPresheaf.naturality_apply (homOfLE le_top).op _).trans (congrArg _ (he a))
  -- The chosen cover uses the open inclusions of its affine members.
  change V.ι ≫ g = V.ι ≫ h
  rw [← g.resLE_comp_ι hg, ← h.resLE_comp_ι hh,
    resLE_eq_of_pullback_toTwistingSheaf hgen e w.property.1 r hg hh hloc]

end AlgebraicGeometry.Proj
