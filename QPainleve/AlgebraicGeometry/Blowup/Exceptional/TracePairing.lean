/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Duality
public import QPainleve.AlgebraicGeometry.Cohomology.Duality.Cartier

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Restriction
import QPainleve.AlgebraicGeometry.Blowup.Projective.Global
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Cohomology.Support
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveLine.Differentials
import TauCeti.AlgebraicGeometry.Curves.Differentials
import TauCeti.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Trace duality for positive exceptional twists

The Cartier sequence of a point blowup relates top-degree Serre pairings at consecutive
exceptional coefficients. Its induced trace pairs on the exceptional projective line with
values in the restriction of the canonical bundle twisted by the exceptional divisor.
The canonical bundle formula and the restriction formula identify this line bundle
with the differential sheaf of the exceptional projective line. Curve duality then
gives perfection for any nonzero induced trace, and Cartier descent transfers perfection
through every positive coefficient.
-/

public noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {p : X} (k : Type u) [Field k] [PerfectField k]
  [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "J" => vanishingIdeal (Closeds.mk (closure (Set.singleton p)) isClosed_closure)
local notation "Y" => blowup J
local notation "π" => blowupToBase J
local notation "E" => comap J π
local notation "i" => subschemeι E
local notation "F" => pullback i
local notation "hE" => isEffectiveCartier_comap_blowupToBase J
local notation "K[" W "]" => QPainleve.canonicalBundle k W 2
local notation "P" => projectiveLine k
local notation "Δ" =>
  InvertibleSheaf.tensorProduct (K[Y])
    (InvertibleSheaf.dual (IsEffectiveCartier.toInvertibleSheaf hE))

variable (hp : IsClosed ({p} : Set X))

private theorem exists_iso_exceptional_trace_bundle
    (hrat : IsIso (X.fromSpecResidueField p ≫ X ↘ S)) :
    let : (Y).Over S := ⟨π ≫ X ↘ S⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
    ∃ e : P ≅ (E).subscheme, e.hom ≫ i ≫ π ≫ X ↘ S = P ↘ S ∧
      Nonempty (((pullback (e.hom ≫ i)).obj (Δ).obj) ≅ (P).relativeDifferentials k) := by
  intro _ _
  have : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  have : IsRegularLocalRing (X.presheaf.stalk p) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ S) p
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq (X ↘ S) 2).mp
    inferInstance).2 p hp
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
  have cmp (I : X.IdealSheafData) (hI : I = (X.fromSpecResidueField p).ker) :
      ∃ e : P ≅ (I.comap I.blowupToBase).subscheme,
        e.hom ≫ (I.comap I.blowupToBase).subschemeι ≫ I.blowupToBase ≫ X ↘ S = P ↘ S ∧
        ∀ (a : LineBundleClass X) (M : InvertibleSheaf I.blowup),
          LineBundleClass.mk M = LineBundleClass.pullback I.blowupToBase a *
            I.blowupExceptionalClass ^ (2 : ℤ) →
          Nonempty (((InvertibleSheaf.pullback
            (e.hom ≫ (I.comap I.blowupToBase).subschemeι)).obj M).obj ≅
              Proj.twistingSheaf 𝒜 (-2)) := by
    subst I
    obtain ⟨e, he, ht⟩ := exists_iso_projectiveLine_pullback_pointBlowup_exceptional_twist
      p k hp hdim hrat
    refine ⟨e, he, fun a M hM ↦ ht a 2 M ?_⟩
    simpa only [blowupExceptionalClass_def, inv_zpow'] using hM
  obtain ⟨e, he, ht⟩ := cmp J (X.ker_fromSpecResidueField_eq_vanishingIdeal p).symm
  have hΔ : LineBundleClass.mk Δ =
      LineBundleClass.pullback π (LineBundleClass.mk (K[X])) *
        (J).blowupExceptionalClass ^ (2 : ℤ) := by
    rw [LineBundleClass.mk_tensorProduct, mk_canonicalBundle_pointBlowup k hp,
      ← LineBundleClass.inv_mk, mul_assoc, zpow_two, blowupExceptionalClass_def]
  obtain ⟨a⟩ := ht _ _ hΔ
  refine ⟨e, he, ⟨(eqToIso (InvertibleSheaf.pullback_obj_obj _ _)).symm ≪≫
    a ≪≫ (projectiveLine.relativeDifferentialsIsoTwistingSheaf k).symm⟩⟩

variable [Infinite k] [X.IsProjectiveOver k]

private theorem isPerfPair_exceptionalRestrictionTrace
    (hrat : IsIso (X.fromSpecResidueField p ≫ X ↘ S)) :
    let : (Y).Over S := ⟨π ≫ X ↘ S⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
    ∀ (tr : Cohomology (K[Y]).obj 2 →ₗ[k] k),
      (hE).cohomologyRestrictionTrace k (K[Y]) 1 tr ≠ 0 →
      ∀ M : InvertibleSheaf Y,
        (cohomologyTracePairing (M := (F).obj M.obj) k 1
          ((hE).cohomologyRestrictionTrace k (K[Y]) 1 tr)).IsPerfPair := by
  intro _ _ tr htr M
  obtain ⟨e, he, ⟨hΩ⟩⟩ := exists_iso_exceptional_trace_bundle k hp hrat
  let : e.hom.IsOver S := ⟨he⟩
  let A := (InvertibleSheaf.pullback i).obj M
  let D := (InvertibleSheaf.pullback i).obj Δ
  let A' := (InvertibleSheaf.pullback e.hom).obj A
  let Ω := InvertibleSheaf.relativeDifferentials k P
  have hD : LineBundleClass.pullback e.hom (LineBundleClass.mk D) = LineBundleClass.mk Ω := by
    refine (LineBundleClass.pullback_mk e.hom D).trans (LineBundleClass.mk_eq_mk_iff.mpr ⟨?_⟩)
    exact eqToIso (InvertibleSheaf.pullback_obj_obj e.hom D) ≪≫
      (pullback e.hom).mapIso (eqToIso (InvertibleSheaf.pullback_obj_obj i Δ)) ≪≫
      (pullbackComp e.hom i).app (Δ).obj ≪≫ hΩ ≪≫
      eqToIso (InvertibleSheaf.relativeDifferentials_obj k P).symm
  let B := D.tensorProduct A.dual
  have hB : LineBundleClass.mk ((InvertibleSheaf.pullback e.hom).obj B) =
      LineBundleClass.mk (Ω.tensorProduct A'.dual) := by
    rw [← LineBundleClass.pullback_mk e.hom B, LineBundleClass.mk_tensorProduct,
      LineBundleClass.pullback_mul, hD, LineBundleClass.mk_tensorProduct, ← LineBundleClass.inv_mk,
      ← LineBundleClass.inv_mk, LineBundleClass.pullback_inv, LineBundleClass.pullback_mk]
  obtain ⟨b⟩ := LineBundleClass.mk_eq_mk_iff.mp hB
  have : (Y).IsProjectiveOver k := (J).isProjectiveOver_blowup_of_isNoetherianRing k
  have : (E).subscheme.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k i
  have : Nonempty (E).subscheme := Nonempty.map e.hom inferInstance
  have : IsIntegral (E).subscheme := isIntegral_of_isOpenImmersion e.inv
  have hd : topologicalKrullDim (E).subscheme = (1 : ℕ) :=
    (e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq).symm.trans
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (P ↘ S) (n := 1))
  let e₁ := e.hom.cohomologyPullbackBaseLinearEquivOfIsIso k A.obj 1
  let e₀ := e.hom.cohomologyPullbackBaseLinearEquivOfIsIso k B.obj 0
  let b₀ := cohomologyBaseLinearEquivOfIso k
    (eqToIso (InvertibleSheaf.pullback_obj_obj e.hom B).symm ≪≫ b) 0
  have hdim : Module.finrank k (Cohomology A.obj 1) =
      Module.finrank k (Cohomology B.obj 0) :=
    e₁.finrank_eq.symm.trans <|
      (finrank_cohomology_one_eq_finrank_cohomology_zero_differentials_tensor_dual_of_smooth
        (k := k) A').trans (b₀.finrank_eq.symm.trans e₀.finrank_eq)
  apply (A.isPerfPair_cohomologyTracePairing_iff_finrank k D hd.le _ htr).mpr
  exact hdim.trans (A.sectionsInternalHomLinearEquiv k D).finrank_eq.symm

private theorem isPerfPair_next_exceptional_twist
    (hrat : IsIso (X.fromSpecResidueField p ≫ X ↘ S)) :
    let : (Y).Over S := ⟨π ≫ X ↘ S⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
    ∀ (tr : Cohomology (K[Y]).obj 2 →ₗ[k] k),
      (hE).cohomologyRestrictionTrace k (K[Y]) 1 tr ≠ 0 →
      ∀ (M : InvertibleSheaf Y),
        (cohomologyTracePairing (M := (M.tensorProduct
          (IsEffectiveCartier.toInvertibleSheaf hE)).obj) k 2 tr).IsPerfPair →
        (cohomologyTracePairing (M := M.obj) k 2 tr).IsPerfPair := by
  intro _ _ tr htr M hprev
  obtain ⟨e, -, -⟩ := exists_iso_exceptional_trace_bundle k hp hrat
  have hdim : topologicalKrullDim (E).subscheme = (1 : ℕ) :=
    (e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq).symm.trans
      (topologicalKrullDim_eq_of_smoothOfRelativeDimension (P ↘ S) (n := 1))
  have : (Y).IsProjectiveOver k := (J).isProjectiveOver_blowup_of_isNoetherianRing k
  have : (E).subscheme.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k i
  let A := (InvertibleSheaf.pullback i).obj M
  have hA : A.obj = (F).obj M.obj := InvertibleSheaf.pullback_obj_obj i M
  have : ((F).obj M.obj).IsQuasicoherent :=
    hA ▸ (inferInstance : A.obj.IsQuasicoherent)
  have hvan : Subsingleton (Cohomology ((F).obj M.obj) 2) :=
    subsingleton_cohomology_of_projective_dim_lt (k := k) _ (by rw [hdim]; norm_num)
  let L := M.tensorProduct (IsEffectiveCartier.toInvertibleSheaf hE)
  have := moduleFinite_cohomology_of_isProjectiveOver k L.obj 2
  have := moduleFinite_cohomology_of_isProjectiveOver k M.obj 2
  let b : L.obj ≅ M.obj ⊗ (E).sheaf :=
    M.tensorProductObjIso _ ≪≫ (tensorLeft M.obj).mapIso
      (eqToIso (IsEffectiveCartier.toInvertibleSheaf_obj hE))
  apply (hE).isPerfPair_cohomologyTracePairing_of_cartier_twist M (K[Y]) 1 tr hvan
  · exact isPerfPair_cohomologyTracePairing_of_iso b 2 tr hprev
  · exact isPerfPair_exceptionalRestrictionTrace k hp hrat tr htr M

variable [IsIntegral X]

/-- Top-degree perfection transfers to every integer exceptional twist once the canonical
Cartier connecting map induces a nonzero trace on the exceptional line. The ambient trace is
the pullback transport of the given trace on the base. -/
theorem isPerfPair_cohomologyTracePairing_of_exceptional_twist
    (hrat : IsIso (X.fromSpecResidueField p ≫ X ↘ S))
    (L : InvertibleSheaf X) (M : InvertibleSheaf Y) (m : ℤ)
    (hM : LineBundleClass.mk M =
      LineBundleClass.pullback π (LineBundleClass.mk L) * (J).blowupExceptionalClass ^ m)
    (tr : Cohomology (K[X]).obj 2 →ₗ[k] k)
    (hbase : (cohomologyTracePairing (M := L.obj) k 2 tr).IsPerfPair) :
    let : (Y).Over S := ⟨π ≫ X ↘ S⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
      smoothOfRelativeDimension_blowup_closed_point (X ↘ S) hp
    let trY := tr.comp (cohomologyCanonicalBundlePointBlowupLinearEquiv k hp 2).symm.toLinearMap
    (hE).cohomologyRestrictionTrace k (K[Y]) 1 trY ≠ 0 →
      (cohomologyTracePairing (M := M.obj) k 2 trY).IsPerfPair := by
  intro _ _ trY htrY
  have htr : tr ≠ 0 := by
    intro he
    apply htrY
    ext x
    simp only [IsEffectiveCartier.cohomologyRestrictionTrace_apply, trY, he,
      LinearMap.zero_comp, LinearMap.zero_apply]
  by_cases hm : m ≤ 1
  · exact (isPerfPair_cohomologyTracePairing_of_exceptional_twist_le_one
      k hp L M hM hm tr htr).mpr hbase
  let a := LineBundleClass.pullback π (LineBundleClass.mk L)
  let b := (J).blowupExceptionalClass
  have hb : LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf hE) = b⁻¹ := by
    dsimp only [b]
    rw [blowupExceptionalClass_def, inv_inv]
  have transfer (n : ℕ) (N : InvertibleSheaf Y)
      (hN : LineBundleClass.mk N = a * b ^ ((n : ℤ) + 1)) :
      (cohomologyTracePairing (M := N.obj) k 2 trY).IsPerfPair := by
    induction n generalizing N with
    | zero =>
      have hN' : LineBundleClass.mk N = a * b ^ (1 : ℤ) := by
        simpa only [Nat.cast_zero, zero_add] using hN
      exact (isPerfPair_cohomologyTracePairing_of_exceptional_twist_le_one
        k hp L N hN' le_rfl tr htr).mpr hbase
    | succ n ih =>
      let prev := N.tensorProduct (IsEffectiveCartier.toInvertibleSheaf hE)
      have hprev : LineBundleClass.mk prev = a * b ^ ((n : ℤ) + 1) := by
        rw [LineBundleClass.mk_tensorProduct, hN, hb, mul_assoc, ← zpow_sub_one]
        congr 2
        omega
      exact isPerfPair_next_exceptional_twist k hp hrat trY htrY N (ih prev hprev)
  let n := (m - 1).toNat
  have hn : (n : ℤ) + 1 = m := by
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  exact transfer n M (hn.symm ▸ hM)

end AlgebraicGeometry.Scheme.IdealSheafData
