/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.RingTheory.ReesAlgebra.Cech
public import TauCeti.AlgebraicGeometry.Cohomology.MayerVietoris
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Basic
import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# Structure-sheaf cohomology of affine blowups

The blowup of an affine scheme in a two-generated ideal has vanishing structure-sheaf
cohomology in positive degrees. For a weakly regular generating pair with regular second
element, the base ring also maps isomorphically to the global functions. This is the affine
calculation used for the structure sheaf of a point blowup of a smooth surface.

Flat base change extends the comparison to finitely generated ideals whose prime
localizations are the unit ideal or admit such a generating pair.

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

section TwoChart

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

end TwoChart

section Affine

open Limits TopologicalSpace
open scoped TensorProduct nonZeroDivisors

private theorem local_blowup_cohomology {A : Type u} [CommRing A] (J : Ideal A)
    (hJ : J = ⊤ ∨ ∃ a b : A, Ideal.span {a, b} = J ∧ IsWeaklyRegular A [a, b] ∧
      b ∈ nonZeroDivisors A) :
    Function.Bijective (Proj.toSpecCoeff (grade J)).appTop ∧
      ∀ n : ℕ, 0 < n → Subsingleton
        (Cohomology (SheafOfModules.unit (Proj (grade J)).ringCatSheaf) n) := by
  rcases hJ with rfl | ⟨a, b, hab, hreg, hb⟩
  · have hspan : Ideal.span {(1 : A)} = ⊤ := by simp
    have : IsIso (Proj.toSpecCoeff (grade (⊤ : Ideal A))) := by
      rw [← hspan, toSpecCoeff_reesAlgebra]
      exact isIso_toSpecZero_reesAlgebra_span_singleton (IsSMulRegular.one A)
    have : IsIso (Proj.toSpecCoeff (grade (⊤ : Ideal A))).appTop :=
      Scheme.Γ.map_isIso (Proj.toSpecCoeff (grade (⊤ : Ideal A))).op
    refine ⟨ConcreteCategory.bijective_of_isIso _, fun n hn ↦ ?_⟩
    have : IsAffine (Proj (grade (⊤ : Ideal A))) :=
      IsAffine.of_isIso (Proj.toSpecCoeff (grade (⊤ : Ideal A)))
    have := isQuasicoherent_structureSheaf (Proj (grade (⊤ : Ideal A)))
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact subsingleton_cohomology_succ_of_isAffine _ q
  · exact ⟨bijective_appTop_toSpecCoeff_reesAlgebra hab hreg hb,
      subsingleton_cohomology_unit_proj_reesAlgebra hab⟩

variable {R : Type u} [CommRing R] (I : Ideal R)
  (A : PrimeSpectrum R → Type u) [∀ P, CommRing (A P)] [∀ P, Algebra R (A P)]
  [loc : ∀ P, IsLocalization P.asIdeal.primeCompl (A P)]

local notation "Bl" => Proj (grade I)
local notation "f" => Proj.toSpecCoeff (grade I)

private theorem isProper_affineBlowup (hI : I.FG) : IsProper f := by
  rw [toSpecCoeff_reesAlgebra]
  exact isProper_toSpecZero_reesAlgebra hI

private theorem subsingleton_baseChange_cohomology_affineBlowup
    {S : Type u} [CommRing S] [Algebra R S] [Module.Flat R S]
    [CompactSpace (Bl)] [QuasiSeparatedSpace (Bl)]
    (h : I.map (algebraMap R S) = ⊤ ∨
      ∃ a b : S, Ideal.span {a, b} = I.map (algebraMap R S) ∧
        IsWeaklyRegular S [a, b] ∧ b ∈ nonZeroDivisors S)
    (n : ℕ) (hn : 0 < n) :
    let : (Bl).Over (Spec (.of R)) := ⟨f⟩
    let M : (Bl).Modules := SheafOfModules.unit (Bl).ringCatSheaf
    let : Module R (Cohomology M n) := cohomologyBaseModule R (Bl) M n
    Subsingleton (S ⊗[R] Cohomology M n) := by
  let : (Bl).Over (Spec (.of R)) := ⟨f⟩
  let M : (Bl).Modules := SheafOfModules.unit (Bl).ringCatSheaf
  have : M.IsQuasicoherent := isQuasicoherent_structureSheaf (Bl)
  let J := I.map (algebraMap R S)
  let Z := Proj (grade J)
  let : Z.Over (Spec (.of S)) := ⟨Proj.toSpecCoeff (grade J)⟩
  let g : Z ⟶ Bl := affineBlowupBaseChangeHom I S ≫
    pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  have H : IsPullback g (Z ↘ Spec (.of S)) (Bl ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := isPullback_affineBlowup_of_flat I S
  let e := cohomologyBaseChangeLinearEquiv H M n
  let e' := (cohomologyFunctor Z n).mapIso (pullbackObjUnitIso g)
  have hZ := (local_blowup_cohomology J h).2 n hn
  have hpull : Subsingleton (Cohomology ((Scheme.Modules.pullback g).obj M) n) :=
    @Equiv.subsingleton _ _ e'.addCommGroupIsoToAddEquiv.toEquiv hZ
  exact @Equiv.subsingleton _ _ e.toEquiv hpull

/-- The structure sheaf of an affine blowup has no positive-degree cohomology if the
finitely generated center ideal is locally the unit ideal or is generated by a weakly
regular pair with regular second element. -/
theorem subsingleton_cohomology_affineBlowup (hI : I.FG)
    (h : ∀ P, (I.map (algebraMap R (A P))) = ⊤ ∨
      ∃ a b : A P, Ideal.span {a, b} = I.map (algebraMap R (A P)) ∧
        IsWeaklyRegular (A P) [a, b] ∧ b ∈ nonZeroDivisors (A P))
    (n : ℕ) (hn : 0 < n) :
    Subsingleton (Cohomology (SheafOfModules.unit (Bl).ringCatSheaf) n) := by
  let : (Bl).Over (Spec (.of R)) := ⟨f⟩
  let M : (Bl).Modules := SheafOfModules.unit (Bl).ringCatSheaf
  let : Module R (Cohomology M n) := cohomologyBaseModule R (Bl) M n
  have := isProper_affineBlowup I hI
  have : CompactSpace (Bl) := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace (Bl) := quasiSeparatedSpace_of_quasiSeparated f
  have hlocal (P : Ideal R) [hP : P.IsMaximal] :
      IsLocalizedModule P.primeCompl
        (TensorProduct.mk R (A ⟨P, hP.isPrime⟩) (Cohomology M n) 1) := by
    have := loc ⟨P, hP.isPrime⟩
    exact IsLocalization.tensorProduct_isLocalizedModule P.primeCompl (A ⟨P, hP.isPrime⟩)
  refine @Module.subsingleton_of_localization_maximal R (Cohomology M n) _ _ _
    (fun P hP ↦ A ⟨P, hP.isPrime⟩ ⊗[R] Cohomology M n) _ _
    (fun P hP ↦ TensorProduct.mk R (A ⟨P, hP.isPrime⟩) (Cohomology M n) 1) hlocal ?_
  intro P hP
  have : IsLocalization P.primeCompl (A ⟨P, hP.isPrime⟩) := loc ⟨P, hP.isPrime⟩
  have : Module.Flat R (A ⟨P, hP.isPrime⟩) := IsLocalization.flat _ P.primeCompl
  exact subsingleton_baseChange_cohomology_affineBlowup I (h ⟨P, hP.isPrime⟩) n hn

/-- Pullback along an affine blowup preserves global functions if the finitely generated
center ideal is locally the unit ideal or is generated by a weakly regular pair with
regular second element. -/
theorem bijective_appTop_affineBlowup (hI : I.FG)
    (h : ∀ P, (I.map (algebraMap R (A P))) = ⊤ ∨
      ∃ a b : A P, Ideal.span {a, b} = I.map (algebraMap R (A P)) ∧
        IsWeaklyRegular (A P) [a, b] ∧ b ∈ nonZeroDivisors (A P)) :
    Function.Bijective (f).appTop := by
  let : (Bl).Over (Spec (.of R)) := ⟨f⟩
  have := isProper_affineBlowup I hI
  have : CompactSpace (Bl) := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace (Bl) := quasiSeparatedSpace_of_quasiSeparated f
  let g (P : PrimeSpectrum R) := Proj.toSpecCoeff (grade (I.map (algebraMap R (A P))))
  let Z (P : PrimeSpectrum R) := Proj (grade (I.map (algebraMap R (A P))))
  let (P : PrimeSpectrum R) : (Z P).Over (Spec (.of (A P))) := ⟨g P⟩
  have (P : PrimeSpectrum R) : Module.Flat R (A P) := IsLocalization.flat _ P.asIdeal.primeCompl
  let G (P : PrimeSpectrum R) : Z P ⟶ Bl := affineBlowupBaseChangeHom I (A P) ≫
    pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (A P))))
  let H (P : PrimeSpectrum R) :
      IsPullback (G P) (Z P ↘ Spec (.of (A P))) (Bl ↘ Spec (.of R))
        (Spec.map (CommRingCat.ofHom (algebraMap R (A P)))) :=
    isPullback_affineBlowup_of_flat I (A P)
  let : Algebra R Γ(Bl, ⊤) :=
    ((Bl).baseRingToStructurePresheaf R).app (Opposite.op ⊤) |>.hom.toAlgebra
  let (P : PrimeSpectrum R) : Algebra (A P) Γ(Z P, ⊤) :=
    ((Z P).baseRingToStructurePresheaf (A P)).app (Opposite.op ⊤) |>.hom.toAlgebra
  let (P : PrimeSpectrum R) : Module R Γ(Z P, ⊤) := Module.compHom _ (algebraMap R (A P))
  let htop (P : PrimeSpectrum R) : (⊤ : (Z P).Opens) = G P ⁻¹ᵁ ⊤ :=
    (Scheme.Hom.preimage_top _).symm
  -- Pullback of functions to the base-changed blowup localizes the section module.
  let σ (P : PrimeSpectrum R) : Γ(Bl, ⊤) →ₗ[R] Γ(Z P, ⊤) :=
    sectionsBaseChange (H P) (htop P).le
  have (P : PrimeSpectrum R) : IsScalarTower R (A P) Γ(Z P, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hlocal (P : PrimeSpectrum R) : IsLocalizedModule P.asIdeal.primeCompl (σ P) :=
    (isLocalizedModule_iff_isBaseChange _ (A P) _).mpr
      (isBaseChange_sectionsBaseChange (H P) isCompact_univ isQuasiSeparated_univ
        (htop P))
  suffices hb : Function.Bijective (algebraMap R Γ(Bl, ⊤)) by
    refine (Function.Bijective.of_comp_iff (f).appTop
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv)).mp ?_
    have heq : ⇑(algebraMap R Γ(Bl, ⊤)) =
        (f).appTop ∘ (Scheme.ΓSpecIso (.of R)).inv := by
      funext r
      exact (ConcreteCategory.congr_hom (Scheme.baseRingToStructurePresheaf_app_top R (Bl)) r).trans
        (baseRingToGlobalSections_apply R (Bl) r)
    rwa [← heq]
  have hsource (P : Ideal R) [hP : P.IsMaximal] :
      IsLocalizedModule.AtPrime P (Algebra.linearMap R (A ⟨P, hP.isPrime⟩)) :=
    (isLocalizedModule_iff_isLocalization' P.primeCompl _).2 (loc ⟨P, hP.isPrime⟩)
  refine @bijective_of_isLocalized_maximal R R Γ(Bl, ⊤) _ _ _ _ _
    (fun P hP ↦ A ⟨P, hP.isPrime⟩) _ _ (fun _ _ ↦ Algebra.linearMap R _) hsource
    (fun P hP ↦ Γ(Z ⟨P, hP.isPrime⟩, ⊤)) _ _ (fun P hP ↦ σ ⟨P, hP.isPrime⟩)
    (fun P hP ↦ hlocal ⟨P, hP.isPrime⟩) (Algebra.linearMap R Γ(Bl, ⊤)) ?_
  intro P hP
  let q : PrimeSpectrum R := ⟨P, hP.isPrime⟩
  have : IsLocalizedModule P.primeCompl (Algebra.linearMap R (A q)) := hsource P
  have : IsLocalizedModule P.primeCompl (σ q) := hlocal q
  -- After localization the structural map is the one for the blowup over the local ring.
  have heq : IsLocalizedModule.map P.primeCompl (Algebra.linearMap R (A q)) (σ q)
      (Algebra.linearMap R Γ(Bl, ⊤)) = (Algebra.linearMap (A q) Γ(Z q, ⊤)).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext P.primeCompl (Algebra.linearMap R (A q)) (σ q)
    apply LinearMap.ext
    intro r
    rw [LinearMap.comp_apply, IsLocalizedModule.map_apply, LinearMap.comp_apply]
    refine (sectionsBaseChange_apply (H q) (htop q).le _).trans ?_
    have hbase := ConcreteCategory.congr_hom
      (baseRingToStructurePresheaf_app_comp_appLE_of_isPullback
        (R := R) (R' := A q) (X := Bl) (Y := Z q) (H q) (htop q).le) r
    have hBl : algebraMap R Γ(Bl, ⊤) r =
        ((Bl).baseRingToStructurePresheaf R).app (Opposite.op ⊤) r := rfl
    have hZ (s : A q) : algebraMap (A q) Γ(Z q, ⊤) s =
        ((Z q).baseRingToStructurePresheaf (A q)).app (Opposite.op ⊤) s := rfl
    simp only [Algebra.linearMap_apply, LinearMap.restrictScalars_apply, hBl, hZ]
    exact hbase
  rw [heq]
  have hmap (r : A q) : algebraMap (A q) Γ(Z q, ⊤) r =
      (g q).appTop ((Scheme.ΓSpecIso (.of (A q))).inv r) := by
    exact (ConcreteCategory.congr_hom (Scheme.baseRingToStructurePresheaf_app_top (A q) (Z q))
      r).trans (baseRingToGlobalSections_apply (A q) (Z q) r)
  exact (funext hmap).symm ▸ ((local_blowup_cohomology _ (h q)).1.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (A q))).inv))

end Affine

end QPainleve
