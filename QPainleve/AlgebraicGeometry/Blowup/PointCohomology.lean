/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange
import QPainleve.AlgebraicGeometry.Blowup.Cohomology
import QPainleve.AlgebraicGeometry.Blowup.RegularPair
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Cohomology.FlatBaseChange
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.ProjectionFormula
import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Linear
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf
import TauCeti.AlgebraicGeometry.Scheme.SectionsBaseChange
import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Structure-sheaf direct images for a point blowup

At a regular closed point of local dimension two, the blowup has trivial structure-sheaf
direct image and vanishing higher direct images. Consequently, pulling back finite locally free
sheaves, including line bundles, preserves their cohomology over the base ring.

We use Tau Ceti's flat base change for sections and cohomology to check the result at maximal
localizations of each affine open. The calculation at the center uses a regular parameter pair.
See [The Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS) for the cohomology
of the blowup of a two-dimensional regular local ring.
-/

public section

open CategoryTheory Limits TopologicalSpace reesAlgebra RingTheory.Sequence
open TauCeti.AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct nonZeroDivisors

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

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
  · exact ⟨QPainleve.bijective_appTop_toSpecCoeff_reesAlgebra hab hreg hb,
      QPainleve.subsingleton_cohomology_unit_proj_reesAlgebra hab⟩

private theorem exists_regular_pair_maximalIdeal {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) :
    ∃ a b : A, Ideal.span {a, b} = IsLocalRing.maximalIdeal A ∧
      IsWeaklyRegular A [a, b] ∧ b ∈ nonZeroDivisors A := by
  obtain ⟨a, b, hab, hreg, hrev, -⟩ :=
    QPainleve.exists_affineBlowupChartOfSpanPair_cover hdim
  have hb := ((isWeaklyRegular_cons_iff A b [a]).mp hrev).1
  exact ⟨a, b, hab, hreg,
    mem_nonZeroDivisors_iff_left.mpr (isSMulRegular_iff_right_eq_zero_of_smul.mp hb)⟩

section Affine

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

private theorem subsingleton_cohomology_affineBlowup (hI : I.FG)
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

private theorem bijective_appTop_affineBlowup (hI : I.FG)
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

section Point

variable {X : Scheme.{u}} {p : X}

local notation "Iₚ" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "π" => blowupToBase Iₚ

private theorem point_blowup_localization {U : X.Opens} (hU : IsAffineOpen U)
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (x : U) :
    letI := X.presheaf.algebra_section_stalk x
    let A := X.presheaf.stalk x
    let J := ((Iₚ).ideal ⟨U, hU⟩).map (algebraMap Γ(X, U) A)
    J = ⊤ ∨ ∃ a b : A, Ideal.span {a, b} = J ∧ IsWeaklyRegular A [a, b] ∧
      b ∈ nonZeroDivisors A := by
  obtain ⟨x, hx⟩ := x
  by_cases he : x = p
  · subst x
    have hJ := map_ideal_vanishingIdeal_closure_singleton_of_specializes
      (U := ⟨U, hU⟩) hx (specializes_rfl : p ⤳ p)
    rw [TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, Ideal.comap_id] at hJ
    exact Or.inr (hJ.symm ▸ exists_regular_pair_maximalIdeal hdim)
  · have hns : ¬ p ⤳ x := by
      simpa [specializes_iff_mem_closure, hp.closure_eq] using he
    exact Or.inl (map_ideal_vanishingIdeal_closure_singleton_of_not_specializes
      (U := ⟨U, hU⟩) hx hns)

variable [IsLocallyNoetherian X]

private theorem point_blowup_affine {U : X.Opens} (hU : IsAffineOpen U)
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    Function.Bijective (Proj.toSpecCoeff (grade ((Iₚ).ideal ⟨U, hU⟩))).appTop ∧
      ∀ n : ℕ, 0 < n → Subsingleton (Cohomology (SheafOfModules.unit
        (Proj (grade ((Iₚ).ideal ⟨U, hU⟩))).ringCatSheaf) n) := by
  let x (P : PrimeSpectrum Γ(X, U)) : U :=
    ⟨hU.fromSpec P, hU.range_fromSpec.subset (Set.mem_range_self P)⟩
  let A (P : PrimeSpectrum Γ(X, U)) : Type u := X.presheaf.stalk (x P)
  let (P : PrimeSpectrum Γ(X, U)) : Algebra Γ(X, U) (A P) :=
    X.presheaf.algebra_section_stalk (x P)
  have (P : PrimeSpectrum Γ(X, U)) : IsLocalization P.asIdeal.primeCompl (A P) :=
    hU.isLocalization_stalk' P (x P).property
  have := IsLocallyNoetherian.component_noetherian (X := X) ⟨U, hU⟩
  let J := (Iₚ).ideal ⟨U, hU⟩
  have hJ : J.FG := IsNoetherian.noetherian _
  have hlocal (P : PrimeSpectrum Γ(X, U)) := point_blowup_localization hU hp hdim (x P)
  exact ⟨bijective_appTop_affineBlowup J A hJ hlocal,
    subsingleton_cohomology_affineBlowup J A hJ hlocal⟩

private theorem isIso_app_pointBlowup_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U)
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) : IsIso ((π).app U) := by
  let f := Proj.toSpecCoeff (grade ((Iₚ).ideal ⟨U, hU⟩))
  have hf : IsIso f.appTop :=
    (ConcreteCategory.isIso_iff_bijective _).2 (point_blowup_affine hU hp hdim).1
  have H := (Iₚ).isPullback_blowupChart hU
  let e := H.isoIsPullback _ _ (isPullback_morphismRestrict π U)
  have he : e.hom ≫ (π ∣_ U) = f ≫ hU.isoSpec.inv :=
    H.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict π U)
  have he' : (π ∣_ U).appTop ≫ e.hom.appTop = hU.isoSpec.inv.appTop ≫ f.appTop :=
    congrArg Scheme.Hom.appTop he
  have h₁ : IsIso e.hom.appTop := Scheme.Γ.map_isIso e.hom.op
  have h₂ : IsIso hU.isoSpec.inv.appTop := Scheme.Γ.map_isIso hU.isoSpec.inv.op
  have hs : IsIso ((π ∣_ U).appTop ≫ e.hom.appTop) :=
    he'.symm ▸ (inferInstance : IsIso (hU.isoSpec.inv.appTop ≫ f.appTop))
  have hπ : IsIso ((π ∣_ U).app ⊤) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ ((π ∣_ U).appTop) e.hom.appTop h₁ hs
  rw [morphismRestrict_app'] at hπ
  have hU' : U.ι ''ᵁ ⊤ = U := by simp
  have hV' : ((π) ⁻¹ᵁ U).ι ''ᵁ ⊤ = (π) ⁻¹ᵁ U := by simp
  rw [Scheme.Hom.app_eq_appLE]
  exact ((π).appLE_congr _ hU' hV' (fun m ↦ IsIso m)).1 hπ

/-- The blowup of a regular closed point of local dimension two induces an isomorphism on
the structure sheaf over every open of the base. -/
theorem isIso_app_pointBlowup
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (U : X.Opens) :
    IsIso ((π).app U) := by
  refine (π).isIso_app_of_isBasis (B := fun V : X.affineOpens ↦ V.val) ?_
    (fun V ↦ isIso_app_pointBlowup_of_isAffineOpen V.property hp hdim) U
  simpa using X.isBasis_affineOpens

/-- All positive higher direct images of the structure sheaf vanish for the blowup of a
regular closed point of local dimension two. -/
theorem isZero_higherDirectImage_succ_unit_pointBlowup
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (n : ℕ) :
    IsZero (((π).higherDirectImage (n + 1)).obj
      (SheafOfModules.unit ((Iₚ).blowup).ringCatSheaf)) := by
  refine (π).isZero_higherDirectImage_succ_of_isBasis _ n X.isBasis_affineOpens fun U hU ↦ ?_
  have h := (point_blowup_affine hU hp hdim).2 (n + 1) (Nat.succ_pos n)
  let g := (Iₚ).blowupChart hU
  have : IsOpenImmersion g := MorphismProperty.of_isPullback
    ((Iₚ).isPullback_blowupChart hU) (inferInstance : IsOpenImmersion U.ι)
  let e := cohomologyOnOpensRangeIso g
    (SheafOfModules.unit ((Iₚ).blowup).ringCatSheaf) (n + 1)
  let e' := (cohomologyFunctor _ (n + 1)).mapIso (restrictUnitIso g)
  rw [← opensRange_blowupChart _ hU]
  exact @Equiv.subsingleton _ _ (e ≪≫ e').addCommGroupIsoToAddEquiv.toEquiv h

/-- The canonical map from the structure sheaf to its direct image along the blowup of
a regular closed point of local dimension two is an isomorphism. -/
theorem isIso_unitToPushforwardObjUnit_pointBlowup
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (π).toRingCatSheafHom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have := isIso_app_pointBlowup hp hdim U
  exact ConcreteCategory.bijective_of_isIso ((π).app U)

open MonoidalCategory

/-- Direct image along the blowup of a regular closed point of local dimension two recovers
each finite locally free sheaf from its pullback. -/
noncomputable def pointBlowupPushforwardPullbackIso
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (E : FiniteLocallyFreeSheaf X) :
    E.obj ≅ (pushforward π).obj ((Scheme.Modules.pullback π).obj E.obj) := by
  have := isIso_unitToPushforwardObjUnit_pointBlowup hp hdim
  let e := asIso (SheafOfModules.unitToPushforwardObjUnit (π).toRingCatSheafHom)
  simpa only [FiniteLocallyFreeSheaf.pullback_obj_obj] using
    (ρ_ E.obj).symm ≪≫ (tensorLeft E.obj).mapIso e ≪≫
      FiniteLocallyFreeSheaf.tensorPushforwardUnitIso π E

/-- Blowup at a regular closed point of local dimension two preserves cohomology of finite
locally free sheaves as modules over the base ring, in every degree. -/
noncomputable def pointBlowupCohomologyLinearEquiv
    (R : Type u) [CommRing R] [X.Over (Spec (.of R))]
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (E : FiniteLocallyFreeSheaf X) (n : ℕ) :
    let : ((Iₚ).blowup).Over (Spec (.of R)) := ⟨π ≫ X ↘ Spec (.of R)⟩
    Cohomology E.obj n ≃ₗ[R] Cohomology ((Scheme.Modules.pullback π).obj E.obj) n := by
  let : ((Iₚ).blowup).Over (Spec (.of R)) := ⟨π ≫ X ↘ Spec (.of R)⟩
  have : (π).IsOver (Spec (.of R)) := ⟨rfl⟩
  have hvan (q : ℕ) : IsZero (((π).higherDirectImage (q + 1)).obj
      ((Scheme.Modules.pullback π).obj E.obj)) := by
    simpa only [FiniteLocallyFreeSheaf.pullback_obj_obj] using
      FiniteLocallyFreeSheaf.isZero_higherDirectImage_pullback π E (q + 1)
        (isZero_higherDirectImage_succ_unit_pointBlowup hp hdim q)
  exact (cohomologyBaseLinearEquivOfIso R (pointBlowupPushforwardPullbackIso hp hdim E) n).trans
    ((π).cohomologyPushforwardBaseLinearEquivOfIsZeroHigherDirectImage R _ hvan n)

end Point

end AlgebraicGeometry.Scheme.IdealSheafData
