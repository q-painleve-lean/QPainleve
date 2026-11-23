/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.VectorBundle.FiniteLocallyFree
import QPainleve.AlgebraicGeometry.Blowup.Cohomology
import QPainleve.AlgebraicGeometry.Blowup.RegularPair
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Affine
import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.ProjectionFormula
import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Linear
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.Morphisms.Flat.StructureSheaf
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
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

private theorem exists_regular_pair_maximalIdeal {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) :
    ∃ a b : A, Ideal.span {a, b} = IsLocalRing.maximalIdeal A ∧
      IsWeaklyRegular A [a, b] ∧ b ∈ nonZeroDivisors A := by
  obtain ⟨a, b, hab, hreg, hrev, -⟩ :=
    QPainleve.exists_affineBlowupChartOfSpanPair_cover hdim
  have hb := ((isWeaklyRegular_cons_iff A b [a]).mp hrev).1
  exact ⟨a, b, hab, hreg,
    mem_nonZeroDivisors_iff_left.mpr (isSMulRegular_iff_right_eq_zero_of_smul.mp hb)⟩

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
  exact ⟨QPainleve.bijective_appTop_affineBlowup J A hJ hlocal,
    QPainleve.subsingleton_cohomology_affineBlowup J A hJ hlocal⟩

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

variable {X : Scheme.{u}} (p : X) [IsLocallyNoetherian X]

local notation "Iₚ" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "π" => blowupToBase Iₚ

/-- Pulling back a line bundle along the blowup of a regular closed point of local
dimension two preserves its cohomology in every degree. -/
theorem nonempty_cohomologyLinearEquiv_pointBlowup_pullback
    (k : Type u) [Field k] [X.Over (Spec (.of k))]
    (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (L : InvertibleSheaf X) (q : ℕ) :
    let : Scheme.Over (blowup Iₚ) (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    Nonempty (Cohomology L.obj q ≃ₗ[k]
      Cohomology ((InvertibleSheaf.pullback π).obj L).obj q) := by
  rw [ker_fromSpecResidueField_eq_vanishingIdeal p]
  exact ⟨pointBlowupCohomologyLinearEquiv k hp hdim
    ((InvertibleSheaf.toFiniteLocallyFree X).obj L) q⟩

end AlgebraicGeometry.Scheme.IdealSheafData
