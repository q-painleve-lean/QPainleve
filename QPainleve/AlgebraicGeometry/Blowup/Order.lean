/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import QPainleve.AlgebraicGeometry.IdealSheaf.PointOrder
public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import QPainleve.AlgebraicGeometry.IdealSheaf.RegularPair
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.RingTheory.Ideal.AffineBlowup.StrictTransform
import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap
import TauCeti.RingTheory.Regular.AssociatedGraded

/-!
# Detection of stalk order on a point blowup

The pullback of an ideal is contained in the `n`-th exceptional power exactly when
its stalk order at the regular closed center is at least `n`. The converse uses the blowup
chart criterion `Ideal.pow_dvd_algebraMap_affineBlowup_iff`.

## References

* P. Hacking, *583C Lecture notes*, Proposition 7.3.
-/

public section

open CategoryTheory TopologicalSpace RingTheory.Sequence

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (p : X)

local notation "Iₚ" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)

private theorem exists_orderOne_blowup_parameter [IsLocallyNoetherian X]
    [IsRegularLocalRing (X.presheaf.stalk p)] (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) :
    ∃ (U : X.affineOpens), p ∈ U.val ∧ ∃ a : Γ(X, U),
      a ∈ (Iₚ).ideal U ∧ a ∉ (Iₚ).ideal U ^ 2 ∧
        NoZeroDivisors ((Iₚ).ideal U).AssociatedGraded := by
  obtain ⟨U, hpU, -, a, b, hspan, hab, -⟩ :=
    exists_mem_le_span_pair_vanishingIdeal_closure_singleton hdim (Opens.mem_top p)
  let P := (Iₚ).ideal U
  have hvanishing := congrArg (fun K : X.IdealSheafData ↦ K.ideal U)
    (X.ker_fromSpecResidueField_eq_vanishingIdeal p)
  have hprime : P = (U.property.primeIdealOf ⟨p, hpU⟩).asIdeal :=
    hvanishing.trans (vanishingIdeal_closure_singleton_ideal p U hpU)
  have : P.IsMaximal := hprime ▸ U.property.primeIdealOf_isMaximal_of_isClosed ⟨p, hpU⟩ hp
  have hlist : Ideal.ofList [a, b] = P := by
    rw [Ideal.ofList_cons, Ideal.ofList_singleton, ← Ideal.span_insert, hspan]
    exact hvanishing.symm
  let : Field (Γ(X, U) ⧸ P) := Ideal.Quotient.field P
  let e := hab.associatedGradedEquiv hlist
  have : NoZeroDivisors P.AssociatedGraded := e.symm.injective.noZeroDivisors _
    (map_zero _) (map_mul _)
  have ha : a ∈ P := hlist ▸ Ideal.subset_span (by simp)
  have ha₂ : a ∉ P ^ 2 := by
    intro h₂
    let i : Fin [a, b].length := 0
    have hv := hab.associatedGradedEquiv_symm_mk_one hlist i
    rw [(Ideal.AssociatedGraded.mk_eq_zero_iff _).mpr (show [a, b][i.val] ∈ P ^ (1 + 1) from h₂),
      map_zero] at hv
    exact MvPolynomial.X_ne_zero _ hv.symm
  exact ⟨U, hpU, a, ha, ha₂, ‹NoZeroDivisors P.AssociatedGraded›⟩

/-- On the blowup of a regular closed point of local dimension two, the largest exceptional
power containing the total transform of an ideal is its stalk order at the center. -/
theorem comap_blowupToBase_le_exceptional_pow_iff [IsIntegral X] [IsLocallyNoetherian X]
    [IsRegularLocalRing (X.presheaf.stalk p)] (hp : IsClosed ({p} : Set X))
    (hdim : ringKrullDim (X.presheaf.stalk p) = 2) (J : X.IdealSheafData) (n : ℕ) :
    J.comap (Iₚ).blowupToBase ≤ ((Iₚ).comap (Iₚ).blowupToBase) ^ n ↔
      (n : ℕ∞) ≤ J.stalkOrder p := by
  rw [← comap_pow]
  refine ⟨fun h ↦ ?_, fun h ↦ comap_mono _ <|
    (natCast_le_stalkOrder_iff_le_pow_ker_fromSpecResidueField p J hp n).mp h⟩
  obtain ⟨U, hpU, a, ha, ha₂, hgr⟩ := exists_orderOne_blowup_parameter p hp hdim
  have hU : IsAffineOpen U.val := U.property
  let P := (Iₚ).ideal U
  have : NoZeroDivisors P.AssociatedGraded := hgr
  exact (natCast_le_stalkOrder_iff_ideal_le_pow p J hp U hpU n).mpr (by
    have : Nonempty U.val := ⟨⟨p, hpU⟩⟩
    have haReg : a ∈ nonZeroDivisors Γ(X, U) :=
      mem_nonZeroDivisors_of_ne_zero fun hzero ↦ ha₂ (hzero ▸ zero_mem _)
    let B := P.affineBlowup a (Localization.Away a)
    let c := TauCeti.AlgebraicGeometry.affineBlowupι (Localization.Away a) ha ≫
      (Iₚ).blowupChart hU
    let ψ := CommRingCat.ofHom (algebraMap Γ(X, U) B)
    have hc : c ≫ (Iₚ).blowupToBase = Spec.map ψ ≫ hU.fromSpec := by
      dsimp only [c, ψ]
      rw [Category.assoc, blowupChart_blowupToBase,
        TauCeti.AlgebraicGeometry.toSpecCoeff_reesAlgebra]
      simp only [Category.assoc]
      exact TauCeti.AlgebraicGeometry.affineBlowupι_toSpecZero_assoc
        (Localization.Away a) ha hU.fromSpec
    have hh : (J.comap (Iₚ).blowupToBase).comap c ≤
        (((Iₚ) ^ n).comap (Iₚ).blowupToBase).comap c := comap_mono c h
    rw [← comap_comp, ← comap_comp, hc] at hh
    have hmap := (comap_SpecMap_fromSpec_le_iff hU ψ).mp hh
    rw [ideal_pow, Pi.pow_apply, CommRingCat.hom_ofHom, Ideal.map_pow,
      Ideal.map_algebraMap_affineBlowup ha, Ideal.span_singleton_pow] at hmap
    intro f hf
    exact (Ideal.pow_dvd_algebraMap_affineBlowup_iff (S := Localization.Away a)
      ha ha₂ haReg n f).mp (Ideal.mem_span_singleton.mp
        (hmap (Ideal.mem_map_of_mem _ hf))))

end AlgebraicGeometry.Scheme.IdealSheafData
