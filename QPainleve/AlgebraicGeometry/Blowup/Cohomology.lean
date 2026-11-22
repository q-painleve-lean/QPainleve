/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.RingTheory.ReesAlgebra.Cech
public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Basic
import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Structure-sheaf cohomology of a two-chart affine blowup

The blowup of an affine scheme in a two-generated ideal has vanishing structure-sheaf
cohomology in positive degrees. For a weakly regular generating pair with regular second
element, the base ring also maps isomorphically to the global functions. This is the affine
calculation used for the structure sheaf of a point blowup of a smooth surface.

The passage from the two-chart section sequence to cohomology uses the Mayer–Vietoris
comparison of Tau Ceti's `projectiveLine` cohomology. The regular local surface case is part of
[The Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS).
-/

public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization RingTheory.Sequence reesAlgebra
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

namespace QPainleve

universe u

variable {R : Type u} [CommRing R] {I : Ideal R} {a b : R}

local notation "𝒜" => grade I
local notation "X" => Proj 𝒜
local notation "ι" => monomialDegreeOne (I := I)
local notation:max "chart(" ha ")" => Proj.basicOpen 𝒜 (ι ha)

private theorem chart_cover (ha : a ∈ I) (hb : b ∈ I) (hI : Ideal.span {a, b} = I) :
    chart(ha) ⊔ chart(hb) = (⊤ : (X).Opens) := by
  have h := iSup_opensRange_affineBlowupι (s := fun i : Bool ↦ cond i a b)
    (by simpa [Bool.range_eq, Set.pair_comm b a] using hI)
  rw [iSup_bool_eq] at h
  simpa only [opensRange_affineBlowupι] using h

private theorem restrict_from_basicOpen {f g : reesAlgebra I} (hg : g ∈ 𝒜 1)
    {x : reesAlgebra I} (hx : x = f * g)
    (hle : Proj.basicOpen 𝒜 x ≤ Proj.basicOpen 𝒜 f) (s : Away 𝒜 f) :
    (X).presheaf.map (homOfLE hle).op (Proj.awayToSection 𝒜 f s) =
      Proj.awayToSection 𝒜 x (awayMap 𝒜 hg hx s) :=
  (ConcreteCategory.congr_hom (Proj.awayMap_awayToSection 𝒜 hg hx) s).symm

private theorem exists_chart_sub_eq (ha : a ∈ I) (hb : b ∈ I) (hI : Ideal.span {a, b} = I)
    (s : Γ(X, chart(ha) ⊓ chart(hb))) :
    ∃ p : Γ(X, chart(ha)), ∃ q : Γ(X, chart(hb)),
      (X).presheaf.map (homOfLE inf_le_left).op p -
        (X).presheaf.map (homOfLE inf_le_right).op q = s := by
  -- Work on the standard open of the product so its sections are homogeneous fractions.
  suffices h : ∀ (W : (X).Opens), Proj.basicOpen 𝒜 (ι ha * ι hb) = W →
      ∀ (hₐ : W ≤ chart(ha)) (hᵦ : W ≤ chart(hb)) (s : Γ(X, W)),
        ∃ p : Γ(X, chart(ha)), ∃ q : Γ(X, chart(hb)),
          (X).presheaf.map (homOfLE hₐ).op p -
            (X).presheaf.map (homOfLE hᵦ).op q = s from
    h _ (Proj.basicOpen_mul 𝒜 _ _) inf_le_left inf_le_right s
  rintro W rfl hₐ hᵦ s
  have hprod := SetLike.mul_mem_graded (monomialDegreeOne_mem_grade ha)
    (monomialDegreeOne_mem_grade hb)
  have hσ : Function.Surjective (Proj.awayToSection 𝒜 (ι ha * ι hb)) :=
    (Proj.basicOpenIsoAway 𝒜 _ hprod two_pos).commRingCatIsoToRingEquiv.surjective
  obtain ⟨w, rfl⟩ := hσ s
  obtain ⟨p, q, rfl⟩ := exists_awayMap_sub_awayMap_eq ha hb hI w
  exact ⟨Proj.awayToSection 𝒜 _ p, Proj.awayToSection 𝒜 _ q, by
    rw [restrict_from_basicOpen (monomialDegreeOne_mem_grade hb) rfl,
      restrict_from_basicOpen (monomialDegreeOne_mem_grade ha) (mul_comm (ι ha) (ι hb))]
    exact (map_sub (Proj.awayToSection 𝒜 (ι ha * ι hb)).hom _ _).symm⟩

private theorem restrict_coeff (ha : a ∈ I) (r : R) :
    (X).presheaf.map (homOfLE (le_top (a := chart(ha)))).op
        ((Proj.toSpecCoeff 𝒜).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) =
      Proj.awayToSection 𝒜 (ι ha)
        ((HomogeneousLocalization.algebra 𝒜 (Submonoid.powers (ι ha))).algebraMap r) := by
  let res := (X).presheaf.map (homOfLE (le_top (a := chart(ha)))).op
  have h : ((Scheme.ΓSpecIso (.of R)).inv ≫ (Proj.toSpecCoeff 𝒜).appTop) ≫ res =
      CommRingCat.ofHom ((HomogeneousLocalization.algebra 𝒜
        (Submonoid.powers (ι ha))).algebraMap) ≫ Proj.awayToSection 𝒜 (ι ha) := by
    have hz : (Proj.toSpecZero 𝒜).appTop ≫ res =
        (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (fromZeroRingHom 𝒜 _) ≫
          Proj.awayToSection 𝒜 (ι ha) :=
      Proj.toSpecZero_appLE_basicOpen 𝒜 (monomialDegreeOne_mem_grade ha) one_pos
    rw [Proj.toSpecCoeff_def, Scheme.Hom.comp_appTop]
    simp only [Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc, hz]
    rw [Iso.inv_hom_id_assoc, ← Category.assoc, ← CommRingCat.ofHom_comp,
      ← HomogeneousLocalization.algebraMap_eq_comp]
  exact ConcreteCategory.congr_hom h r

private theorem chart_functions_agree (ha : a ∈ I) (hb : b ∈ I) (s : Γ(X, ⊤))
    {p : Away 𝒜 (ι ha)} {q : Away 𝒜 (ι hb)}
    (hp : Proj.awayToSection 𝒜 (ι ha) p = (X).presheaf.map (homOfLE le_top).op s)
    (hq : Proj.awayToSection 𝒜 (ι hb) q = (X).presheaf.map (homOfLE le_top).op s) :
    awayMap 𝒜 (monomialDegreeOne_mem_grade hb) rfl p =
      awayMap 𝒜 (monomialDegreeOne_mem_grade ha) (mul_comm (ι ha) (ι hb)) q := by
  have hprod := SetLike.mul_mem_graded (monomialDegreeOne_mem_grade ha)
    (monomialDegreeOne_mem_grade hb)
  have hₐ := (Proj.basicOpen_mul 𝒜 (ι ha) (ι hb)).trans_le inf_le_left
  have hᵦ := (Proj.basicOpen_mul 𝒜 (ι ha) (ι hb)).trans_le inf_le_right
  have hσ : Function.Injective (Proj.awayToSection 𝒜 (ι ha * ι hb)) :=
    (Proj.basicOpenIsoAway 𝒜 _ hprod two_pos).commRingCatIsoToRingEquiv.injective
  apply hσ
  rw [← restrict_from_basicOpen (monomialDegreeOne_mem_grade hb) rfl hₐ,
    ← restrict_from_basicOpen (monomialDegreeOne_mem_grade ha) (mul_comm (ι ha) (ι hb)) hᵦ,
    hp, hq, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2

/-- The affine blowup in a weakly regular generating pair with regular second element has
the same global functions as its base, via pullback along its structure morphism. -/
theorem bijective_appTop_toSpecCoeff_reesAlgebra (hI : Ideal.span {a, b} = I)
    (hab : IsWeaklyRegular R [a, b]) (hb' : b ∈ nonZeroDivisors R) :
    Function.Bijective (Proj.toSpecCoeff (grade I)).appTop := by
  let ha : a ∈ I := hI ▸ Ideal.subset_span (by simp)
  let hb : b ∈ I := hI ▸ Ideal.subset_span (by simp)
  have hChart {c : R} (hc : c ∈ I) : Function.Bijective (Proj.awayToSection 𝒜 (ι hc)) :=
    (Proj.basicOpenIsoAway 𝒜 _ (monomialDegreeOne_mem_grade hc)
      one_pos).commRingCatIsoToRingEquiv.bijective
  suffices h : Function.Bijective (fun r : R ↦
      (Proj.toSpecCoeff 𝒜).appTop ((Scheme.ΓSpecIso (.of R)).inv r)) from
    (Function.Bijective.of_comp_iff _
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.bijective).mp h
  refine ⟨fun r t h ↦ ?_, fun s ↦ ?_⟩
  · apply injective_algebraMap_away_monomialDegreeOne hb hb'
    apply (hChart hb).injective
    rw [← restrict_coeff hb r, ← restrict_coeff hb t]
    exact congrArg ((X).presheaf.map (homOfLE le_top).op) h
  · obtain ⟨p, hp⟩ := (hChart ha).surjective ((X).presheaf.map (homOfLE le_top).op s)
    obtain ⟨q, hq⟩ := (hChart hb).surjective ((X).presheaf.map (homOfLE le_top).op s)
    obtain ⟨r, rfl, rfl⟩ :=
      (awayMap_eq_iff_exists_eq_algebraMap ha hb hab hb').mp (chart_functions_agree ha hb s hp hq)
    refine ⟨r, (X).sheaf.eq_of_locally_eq₂ (homOfLE (le_top (a := chart(ha))))
      (homOfLE (le_top (a := chart(hb)))) (chart_cover ha hb hI).ge _ _ ?_ ?_⟩
    · exact (restrict_coeff ha r).trans hp
    · exact (restrict_coeff hb r).trans hq

/-- The structure sheaf of the blowup of an affine scheme in a two-generated ideal has
no positive-degree cohomology. -/
theorem subsingleton_cohomology_unit_proj_reesAlgebra (hI : Ideal.span {a, b} = I)
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Cohomology (SheafOfModules.unit (X).ringCatSheaf) n) := by
  let ha : a ∈ I := hI ▸ Ideal.subset_span (by simp)
  let hb : b ∈ I := hI ▸ Ideal.subset_span (by simp)
  let M : (X).Modules := SheafOfModules.unit (X).ringCatSheaf
  have : M.IsQuasicoherent := TauCeti.AlgebraicGeometry.isQuasicoherent_structureSheaf X
  have hcov := chart_cover ha hb hI
  have hU {c : R} (hc : c ∈ I) : IsAffineOpen (chart(hc)) :=
    Proj.isAffineOpen_basicOpen 𝒜 _ (monomialDegreeOne_mem_grade hc) one_pos
  have hacyclic {c : R} (hc : c ∈ I) : Subsingleton (cohomologyOn M 1 (chart(hc))) := by
    have : (Scheme.Modules.restrict M (chart(hc)).ι).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_restrictFunctor _ M
    exact subsingleton_cohomologyOn_succ_of_isAffineOpen M (hU hc) 0
  by_cases h : n = 1
  · subst n
    have hdiff : (mayerVietorisSectionsDifference M (chart(ha)) (chart(hb))).range = ⊤ := by
      apply AddMonoidHom.range_eq_top.mpr
      intro s
      obtain ⟨p, q, hpq⟩ := exists_chart_sub_eq ha hb hI s
      exact ⟨(p, q), (mayerVietorisSectionsDifference_apply M _ _ p q).trans hpq⟩
    have hquot : Subsingleton (Γ(M, chart(ha) ⊓ chart(hb)) ⧸
        (mayerVietorisSectionsDifference M (chart(ha)) (chart(hb))).range) := by
      rw [hdiff]
      exact QuotientAddGroup.subsingleton_quotient_top
    exact (sectionsQuotientEquivCohomologyOne M _ _ hcov
      (hacyclic ha) (hacyclic hb)).symm.toEquiv.subsingleton
  · have hW : IsAffineOpen (chart(ha) ⊓ chart(hb)) :=
      Proj.basicOpen_mul 𝒜 _ _ ▸ Proj.isAffineOpen_basicOpen 𝒜 _
        (SetLike.mul_mem_graded (monomialDegreeOne_mem_grade ha)
          (monomialDegreeOne_mem_grade hb)) two_pos
    exact Scheme.Modules.subsingleton_cohomology_of_two_le_of_isAffineOpen M
      (hU ha) (hU hb) hW hcov n (by omega)

end QPainleve
