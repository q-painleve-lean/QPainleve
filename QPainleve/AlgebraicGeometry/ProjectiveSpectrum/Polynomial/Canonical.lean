/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Forms
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.Chart.Sections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
public import QPainleve.AlgebraicGeometry.Modules.ExteriorPower.Sections
import TauCeti.AlgebraicGeometry.Modules.AffineRestriction
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Hom
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# The canonical bundle of the projective plane

The relative two-forms on the polynomial projective plane over a commutative ring
are isomorphic to `𝒪(-3)`. The cyclically ordered affine coordinates give local
generators whose changes of basis are the cubes of the homogeneous ratios.

The construction follows the chart comparison in Tau Ceti's
`projectiveLine.relativeDifferentialsIsoTwistingSheaf`, using Mathlib's basis
of polynomial Kähler differentials and exterior powers.
-/

public noncomputable section

open CategoryTheory Opposite
open TauCeti.AlgebraicGeometry TauCeti.MvPolynomial
open scoped TensorProduct

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin 3) R
local notation "ℙ" => Proj 𝒜
local notation "U[" i "]" => basicOpen 𝒜 (MvPolynomial.X i)
local notation "T" => twistingSheaf 𝒜 (-3)

/-- The coefficient morphism is the base map for relative differentials of the plane. -/
local instance planeOver : (ℙ).Over (Spec (.of R)) := ⟨toSpecCoeff 𝒜⟩

local notation "Ω₁" => Scheme.relativeDifferentials R ℙ
local notation "Ω₂" => Functor.obj (SheafOfModules.exteriorPower (Scheme.sheaf ℙ) 2) Ω₁

local instance planeSmooth : SmoothOfRelativeDimension 2 (ℙ ↘ Spec (.of R)) :=
  smoothOfRelativeDimension_polynomial R

private theorem X_mem_one (i : Fin 3) : MvPolynomial.X i ∈ 𝒜 1 :=
  (MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X R i)

private theorem affine_coordinateOpen (i : Fin 3) : IsAffineOpen U[i] :=
  isAffineOpen_basicOpen 𝒜 _ (X_mem_one R i) one_pos

private theorem iSup_coordinateOpen : (⨆ i : Fin 3, U[i]) = ⊤ :=
  iSup_basicOpen_eq_top _ _ (MvPolynomial.irrelevant_eq_span_X (Fin 3) R).le

private def cyclicOrder (i : Fin 3) : Equiv.Perm (Fin 2) :=
  if i = 1 then Equiv.swap 0 1 else Equiv.refl _

private theorem cyclicOrder_coordinate (i : Fin 3) (j : Fin 2) :
    i.succAbove ((cyclicOrder i).symm j) = i + j.succ := by
  fin_cases i <;> fin_cases j <;> decide

private def chartDifferentialBasis (i : Fin 3) :
    Module.Basis (Fin 2) Γ(ℙ, U[i]) Γ(Ω₁, U[i]) := by
  let S := Γ(ℙ, U[i])
  let A := MvPolynomial (Fin 2) R
  letI : Algebra R S := (((ℙ).baseRingToStructurePresheaf R).app (op U[i])).hom.toAlgebra
  let e := polynomialChartSectionsEquiv R i
  letI : Algebra A S := e.toAlgHom.toAlgebra
  letI : IsScalarTower R A S := IsScalarTower.of_algHom e.toAlgHom
  let e' : A ≃ₐ[A] S := { __ := e.toRingEquiv, commutes' _ := rfl }
  letI : Algebra.FormallyEtale A S := Algebra.FormallyEtale.of_equiv e'
  exact (((KaehlerDifferential.mvPolynomialBasis R (Fin 2)).baseChange S).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S ≪≫ₗ
      relativeDifferentialsSectionsEquiv R ℙ ⟨U[i], affine_coordinateOpen R i⟩)).reindex
        (cyclicOrder i)

private theorem chartDifferentialBasis_apply (i : Fin 3) (j : Fin 2) :
    chartDifferentialBasis R i j =
      ((ℙ).universalDerivation R).d
        (polynomialCoordinateRatio i (i + j.succ) (le_rfl : U[i] ≤ U[i])) := by
  simp only [chartDifferentialBasis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Module.Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    LinearEquiv.trans_apply, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, RingHom.algebraMap_toAlgebra,
    polynomialCoordinateRatio_self_open]
  let S := Γ(ℙ, U[i])
  let : Algebra R S := (((ℙ).baseRingToStructurePresheaf R).app (op U[i])).hom.toAlgebra
  let U : (ℙ).affineOpens := ⟨U[i], affine_coordinateOpen R i⟩
  let x := polynomialChartSectionsEquiv R i (MvPolynomial.X ((cyclicOrder i).symm j))
  have hx := (polynomialChartSectionsEquiv_X R i ((cyclicOrder i).symm j)).trans
    (congrArg (fun t ↦ awayToSection 𝒜 (MvPolynomial.X i) (awayXRatio i t))
      (cyclicOrder_coordinate i j))
  exact (congrArg (relativeDifferentialsSectionsEquiv R ℙ U)
    (one_smul S (KaehlerDifferential.D R S x))).trans
      ((relativeDifferentialsSectionsEquiv_D R ℙ U x).trans
        (congrArg ((ℙ).universalDerivation R).d hx))

private def wedge (V : (ℙ).Opens) : Γ(Ω₁, V) [⋀^(Fin 2)]→ₗ[Γ(ℙ, V)] Γ(Ω₂, V) :=
  (Scheme.Modules.exteriorPowerSections Ω₁ V 2).hom.compAlternatingMap
    ModuleCat.exteriorPower.mk

private def formOn (i : Fin 3) {V : (ℙ).Opens} (h : V ≤ U[i]) : Γ(Ω₂, V) :=
  wedge R V fun j ↦ ((ℙ).universalDerivation R).d (polynomialCoordinateRatio i (i + j.succ) h)

private theorem res_formOn {U V : (ℙ).Opens} (f : V ⟶ U) (i : Fin 3) (hi : U ≤ U[i]) :
    (Ω₂).val.map f.op (formOn R i hi) = formOn R i (f.le.trans hi) := by
  let D := (ℙ).universalDerivation R
  -- Use the restriction formula for the sectionwise wedge before changing its factors.
  change (Ω₂).val.map f.op (Scheme.Modules.exteriorPowerSections Ω₁ U 2
    (ModuleCat.exteriorPower.mk (fun j ↦ D.d (polynomialCoordinateRatio i (i + j.succ) hi)))) = _
  refine (Scheme.Modules.restrict_exteriorPowerSections_mk Ω₁ f 2 _).trans ?_
  exact congrArg (fun m : Fin 2 → Γ(Ω₁, V) ↦
      Scheme.Modules.exteriorPowerSections Ω₁ V 2 (ModuleCat.exteriorPower.mk m))
    (funext fun j ↦ (D.d_map f.op _).symm.trans (congrArg D.d
      (res_polynomialCoordinateRatio f i (i + j.succ) hi)))

private theorem finTwoOrderEmb_univ :
    (Finset.univ : Finset (Fin 2)).orderEmbOfFin (by simp) = RelEmbedding.refl _ := by
  exact (Finset.orderEmbOfFin_unique' _ (fun _ ↦ Finset.mem_univ _)).symm

private theorem bijective_smul_formOn (i : Fin 3) :
    Function.Bijective (fun a : Γ(ℙ, U[i]) ↦
      a • formOn R i le_rfl) := by
  let S := Γ(ℙ, U[i])
  let b := (chartDifferentialBasis R i).exteriorPower 2
  let J := Set.powersetCard (Fin 2) 2
  let s : J := ⟨Finset.univ, Finset.card_fin 2⟩
  let : Unique J := ⟨⟨s⟩, fun t ↦ Subtype.ext
    (Finset.eq_univ_of_card (s := t.val) (t.property.trans (Fintype.card_fin 2).symm))⟩
  have hb : b s = exteriorPower.ιMulti S 2 (chartDifferentialBasis R i) := by
    -- The unique two-element subset lists both coordinates in their original order.
    rw [exteriorPower.basis_apply]
    rw [exteriorPower.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply]
    have horder : s.val.orderEmbOfFin s.property = RelEmbedding.refl _ := finTwoOrderEmb_univ
    rw [horder]
    rfl
  let e := (LinearEquiv.piUnique S (fun _ : J ↦ S)).symm ≪≫ₗ b.equivFun.symm
  have h (a : S) : e a = a • b s := by
    simp [e, Module.Basis.equivFun_symm_apply, show (default : J) = s from rfl]
  have he := Scheme.Modules.bijective_exteriorPowerSections Ω₁ (affine_coordinateOpen R i) 2
  have hc := he.comp e.bijective
  have heq (a : S) : (Scheme.Modules.exteriorPowerSections Ω₁ U[i] 2) (e a) =
      a • formOn R i le_rfl := by
    rw [h, hb]
    erw [LinearMap.map_smul]
    exact congrArg (fun m : Fin 2 → Γ(Ω₁, U[i]) ↦ a • wedge R U[i] m)
      (funext (chartDifferentialBasis_apply R i))
  exact (show Function.Bijective (fun a : S ↦ a • formOn R i le_rfl) from
    (funext heq) ▸ hc)

private theorem wedge_transition {V : (ℙ).Opens} (a c : Γ(ℙ, V))
    (da db dc dd : Γ(Ω₁, V)) (hda : da = -(a ^ 2) • dd)
    (hdb : db = a • dc + c • da) :
    wedge R V ![da, db] = a ^ 3 • wedge R V ![dc, dd] := by
  let w := wedge R V
  have hu (x y z : Γ(Ω₁, V)) : Function.update ![x, y] 1 z = ![x, z] := by
    funext j
    fin_cases j <;> simp [Function.update]
  have hv (x y z : Γ(Ω₁, V)) : Function.update ![x, y] 0 z = ![z, y] := by
    funext j
    fin_cases j <;> simp [Function.update]
  have hdrop : w ![da, db] = a • w ![da, dc] := by
    rw [hdb]
    have hsum := w.map_update_add ![da, da] 1 (a • dc) (c • da)
    simp only [hu] at hsum
    rw [hsum]
    have h₁ := w.map_update_smul ![da, dc] 1 a dc
    have h₂ := w.map_update_smul ![da, da] 1 c da
    simp only [hu] at h₁ h₂
    have hzero : w ![da, da] = 0 :=
      w.map_eq_zero_of_eq ![da, da] (by simp) (show (0 : Fin 2) ≠ 1 by decide)
    rw [h₁, h₂, hzero, smul_zero, add_zero]
  have hswap : w ![dd, dc] = -w ![dc, dd] := by
    have e : ![dd, dc] = ![dc, dd] ∘ Equiv.swap 0 1 := by
      funext j
      fin_cases j <;> simp
    exact e ▸ (w.map_swap ![dc, dd] (show (0 : Fin 2) ≠ 1 by decide))
  have hmul : w ![da, dc] = a ^ 2 • w ![dc, dd] := by
    rw [hda]
    have h₁ := w.map_update_smul ![dd, dc] 0 (-(a ^ 2)) dd
    simp only [hv] at h₁
    rw [h₁, hswap, neg_smul, smul_neg, neg_neg]
  exact hdrop.trans ((congrArg (a • ·) hmul).trans
    (by rw [smul_smul, ← pow_succ']))

private theorem formOn_succ (i : Fin 3) {V : (ℙ).Opens}
    (hi : V ≤ U[i]) (hj : V ≤ U[i + 1]) :
    formOn R i hi = polynomialCoordinateRatio i (i + 1) hi ^ 3 • formOn R (i + 1) hj := by
  let a := polynomialCoordinateRatio i (i + 1) hi
  let b := polynomialCoordinateRatio i (i + 2) hi
  let c := polynomialCoordinateRatio (i + 1) (i + 2) hj
  let d := polynomialCoordinateRatio (i + 1) i hj
  let D := (ℙ).universalDerivation R
  let w := wedge R V
  have hab : a * c = b := polynomialCoordinateRatio_mul i (i + 1) (i + 2) hi hj
  have had : a * d = 1 := (polynomialCoordinateRatio_mul i (i + 1) i hi hj).trans
    (polynomialCoordinateRatio_self i hi)
  have hdb : D.d b = a • D.d c + c • D.d a := by rw [← hab, D.d_mul]
  have hzero : a • D.d d + d • D.d a = 0 := by rw [← D.d_mul, had, D.d_one]
  have hda : D.d a = -(a ^ 2) • D.d d := by
    calc
      D.d a = (a * d) • D.d a := by rw [had, one_smul]
      _ = a • (d • D.d a) := (smul_smul _ _ _).symm
      _ = -(a ^ 2) • D.d d := by
        rw [eq_neg_of_add_eq_zero_right hzero, smul_neg, smul_smul, pow_two, neg_smul]
  have hforms : formOn R (i + 1) hj = w ![D.d c, D.d d] := by
    unfold formOn
    congr 1
    funext j
    fin_cases j
    · congr 2
      exact add_assoc i 1 1
    · congr 2
      rw [add_assoc]
      exact add_zero i
  rw [hforms]
  have hf : formOn R i hi = w ![D.d a, D.d b] := by
    unfold formOn
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [hf]
  exact wedge_transition R a c (D.d a) (D.d b) (D.d c) (D.d d) hda hdb

private def twistOn (i : Fin 3) {V : (ℙ).Opens} (hi : V ≤ U[i]) : Γ(T, V) :=
  twistingSheaf.chartGenerator (-3) (MvPolynomial.X i) (X_mem_one R i) V hi

private theorem twistOn_transition (i j : Fin 3) {V : (ℙ).Opens}
    (hi : V ≤ U[i]) (hj : V ≤ U[j]) :
    twistOn R i hi = polynomialCoordinateRatio i j hi ^ 3 • twistOn R j hj := by
  apply twistingSheaf.ext
  intro x
  let := x.val.isPrime
  rw [twistOn, twistingSheaf.smul_apply]
  have hp : ((polynomialCoordinateRatio i j hi ^ 3).val x).val =
      ((polynomialCoordinateRatio i j hi).val x).val ^ 3 := by
    erw [AlgebraicGeometry.Proj.pow_apply, HomogeneousLocalization.val_pow]
  rw [hp, val_polynomialCoordinateRatio, twistOn]
  simp only [twistingSheaf.chartGenerator_apply]
  norm_num only
  rw [Localization.mk_pow, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  -- Cross multiplication expresses the change from the generator at j to the one at i.
  change (MvPolynomial.X i ^ 3 * MvPolynomial.X j ^ 3) * 1 =
    MvPolynomial.X i ^ 3 * (MvPolynomial.X j ^ 3 * 1)
  ring

private def fromTwistLocal (i : Fin 3) : (T).over U[i] ⟶ (Ω₂).over U[i] :=
  (twistingSheaf.chartIso (-3) (MvPolynomial.X i) (X_mem_one R i) U[i] le_rfl).inv ≫
    ((Ω₂).over U[i]).unitHomEquiv.symm
      (((Ω₂).overSectionsEquiv U[i]).symm (formOn R i le_rfl))

private theorem fromTwistLocal_app (i : Fin 3) {V : (ℙ).Opens} (hi : V ≤ U[i])
    (m : Γ(T, V)) :
    (fromTwistLocal R i).val.app (op (Over.mk (homOfLE hi))) m =
      (twistingSheaf.chartSectionsLinearEquiv (-3) (MvPolynomial.X i)
        (X_mem_one R i) V hi).symm m • formOn R i hi := by
  -- Evaluating the composite over the slice keeps all scalar structures on Γ(ℙ,V).
  dsimp only [fromTwistLocal]
  change ((((Ω₂).over U[i]).unitHomEquiv.symm
    (((Ω₂).overSectionsEquiv U[i]).symm (formOn R i le_rfl))).val.app
      (op (Over.mk (homOfLE hi))))
    ((twistingSheaf.chartIso (-3) (MvPolynomial.X i) (X_mem_one R i) U[i] le_rfl).inv.val.app
      (op (Over.mk (homOfLE hi))) m) = _
  rw [twistingSheaf.chartIso_inv_app_apply]
  erw [TauCeti.SheafOfModules.unitHomEquiv_symm_val_app,
    SheafOfModules.overSectionsEquiv_symm_apply_eval]
  erw [res_formOn R (homOfLE hi) i le_rfl]
  rfl

private theorem fromTwistLocal_twistOn (i : Fin 3) {V : (ℙ).Opens} (hi : V ≤ U[i]) :
    (fromTwistLocal R i).val.app (op (Over.mk (homOfLE hi))) (twistOn R i hi) =
      formOn R i hi := by
  rw [fromTwistLocal_app]
  have h := twistingSheaf.chartSectionsLinearEquiv_apply (-3)
    (MvPolynomial.X i) (X_mem_one R i) V hi 1
  rw [one_smul] at h
  erw [twistOn, ← h, LinearEquiv.symm_apply_apply, one_smul]

private theorem fromTwistLocal_compatible_succ (i : Fin 3) (V : (ℙ).Opens)
    (hi : V ≤ U[i]) (hj : V ≤ U[i + 1]) (m : Γ(T, V)) :
    (fromTwistLocal R i).val.app (op (Over.mk (homOfLE hi))) m =
      (fromTwistLocal R (i + 1)).val.app (op (Over.mk (homOfLE hj))) m := by
  let fi : Γ(T, V) →ₗ[Γ(ℙ, V)] Γ(Ω₂, V) :=
    ((fromTwistLocal R i).val.app (op (Over.mk (homOfLE hi)))).hom
  let fj : Γ(T, V) →ₗ[Γ(ℙ, V)] Γ(Ω₂, V) :=
    ((fromTwistLocal R (i + 1)).val.app (op (Over.mk (homOfLE hj)))).hom
  let e := twistingSheaf.chartSectionsLinearEquiv (-3)
    (MvPolynomial.X i) (X_mem_one R i) V hi
  have hgen : fi (twistOn R i hi) = fj (twistOn R i hi) := by
    have hf : fi (twistOn R i hi) = formOn R i hi := fromTwistLocal_twistOn R i hi
    have hg : fj (twistOn R (i + 1) hj) = formOn R (i + 1) hj :=
      fromTwistLocal_twistOn R (i + 1) hj
    rw [hf, twistOn_transition R i (i + 1) hi hj, fj.map_smul, hg]
    exact formOn_succ R i hi hj
  have hm : e.symm m • twistOn R i hi = m := by
    simpa only [e, twistOn, twistingSheaf.chartSectionsLinearEquiv_apply] using
      e.apply_symm_apply m
  -- The maps between the slice sections are linear over the same section ring.
  change fi m = fj m
  rw [← hm, fi.map_smul, fj.map_smul, hgen]

private theorem fromTwistLocal_compatible (i j : Fin 3) (V : (ℙ).Opens)
    (hi : V ≤ U[i]) (hj : V ≤ U[j]) (m : Γ(T, V)) :
    (fromTwistLocal R i).val.app (op (Over.mk (homOfLE hi))) m =
      (fromTwistLocal R j).val.app (op (Over.mk (homOfLE hj))) m := by
  by_cases h : j = i
  · subst j
    rfl
  · have hcases : j = i + 1 ∨ i = j + 1 := by
      fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | decide
    rcases hcases with rfl | rfl
    · exact fromTwistLocal_compatible_succ R i V hi hj m
    · exact (fromTwistLocal_compatible_succ R j V hj hi m).symm

private def fromTwist : T ⟶ Ω₂ :=
  SheafOfModules.glueOfOpenCover (X := (ℙ).toTopCat) (ι := Fin 3)
    (T : (ℙ).Modules) Ω₂ (fun i ↦ U[i]) (iSup_coordinateOpen R)
    (fromTwistLocal R) (fromTwistLocal_compatible R)

private theorem fromTwist_app (i : Fin 3) {V : (ℙ).Opens} (hi : V ≤ U[i])
    (m : Γ(T, V)) :
    (fromTwist R).app V m =
      (twistingSheaf.chartSectionsLinearEquiv (-3) (MvPolynomial.X i)
        (X_mem_one R i) V hi).symm m • formOn R i hi :=
  (SheafOfModules.glueOfOpenCover_app (X := (ℙ).toTopCat) (ι := Fin 3)
    (T : (ℙ).Modules) Ω₂ (fun i ↦ U[i]) (iSup_coordinateOpen R)
    (fromTwistLocal R) (fromTwistLocal_compatible R) i V hi m).trans
    (fromTwistLocal_app R i hi m)

private instance isIso_fromTwist : IsIso (fromTwist R) := by
  let := SmoothOfRelativeDimension.smooth 2 (ℙ ↘ Spec (.of R))
  let : (T).IsQuasicoherent := isQuasicoherent_twistingSheaf 𝒜 (-3)
  let : (Ω₂).IsQuasicoherent :=
    ((FiniteLocallyFreeSheaf.differentialForms_obj R ℙ 2).trans
      (differentialForms_def R ℙ 2)) ▸ inferInstanceAs
        ((FiniteLocallyFreeSheaf.differentialForms R ℙ 2).obj.IsQuasicoherent)
  refine Scheme.Modules.Hom.isIso_of_bijective_app (fromTwist R)
    (affine_coordinateOpen R) (iSup_coordinateOpen R) fun i ↦ ?_
  let e := twistingSheaf.chartSectionsLinearEquiv (-3) (MvPolynomial.X i)
    (X_mem_one R i) U[i] le_rfl
  have h := (bijective_smul_formOn R i).comp e.symm.bijective
  exact (funext (fromTwist_app R i le_rfl)) ▸ h

/-- The canonical bundle of the polynomial projective plane over a commutative ring,
given by its sheaf of relative two-forms, is the twist `𝒪(-3)`. -/
def differentialFormsTwoIsoTwistingSheaf :
    Ω₂ ≅ T :=
  (asIso (fromTwist R)).symm

/-- The inverse comparison sends the local twisting generator to the wedge of the two
affine coordinate differentials in cyclic order, on every subopen of a standard chart. -/
@[simp]
theorem differentialFormsTwoIsoTwistingSheaf_inv_app_chartGenerator
    (i : Fin 3) {V : (ℙ).Opens} (hi : V ≤ U[i]) :
    dsimp% only [sheafCompose_obj_obj, Functor.comp_obj, CommRingCat.forgetToRingCat_obj]
    (differentialFormsTwoIsoTwistingSheaf R).inv.val.app (op V)
        (twistingSheaf.chartGenerator (-3) (MvPolynomial.X i)
          ((MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X R i))
          V hi) =
      Scheme.Modules.exteriorPowerSections Ω₁ V 2 (ModuleCat.exteriorPower.mk (fun j ↦
        ((ℙ).universalDerivation R).d (polynomialCoordinateRatio i (i + j.succ) hi))) := by
  exact (SheafOfModules.glueOfOpenCover_app (X := (ℙ).toTopCat) (ι := Fin 3)
    (T : (ℙ).Modules) Ω₂ (fun j ↦ U[j]) (iSup_coordinateOpen R)
    (fromTwistLocal R) (fromTwistLocal_compatible R) i V hi (twistOn R i hi)).trans
    (fromTwistLocal_twistOn R i hi)

end AlgebraicGeometry.Proj
