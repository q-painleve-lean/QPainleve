/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.SectionDivision
public import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf

import QPainleve.AlgebraicGeometry.CartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Product
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Fibers of projective morphisms from sections

The zero ideals of the defining coordinates can identify a closed point fiber
with a reduced effective Cartier divisor.
-/

public noncomputable section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {E : X.IdealSheafData}

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "ℙ[" R "," ι "]" => Proj (MvPolynomial.homogeneousSubmodule ι R)

/-- A closed point fiber with the support of a reduced effective Cartier divisor is that
divisor if some defining coordinates come from sections of the Cartier twist that generate
along the divisor. -/
theorem IsEffectiveCartier.comap_ker_of_projective_sections [IsIntegral X]
    {k : Type u} [Field k] {ι ι' : Type u} (hE : E.IsEffectiveCartier)
    (M : InvertibleSheaf X) (f : X ⟶ Spec (.of k))
    (v : ι → Γ(M.obj, ⊤)) (hv : (⨆ i, M.obj.nonvanishingLocus (v i)) = ⊤)
    (t : ι' → Γ((hE.toInvertibleSheaf.tensorProduct M).obj, ⊤)) (a : ι' → ι)
    (ha : ∀ i, v (a i) = (M.idealTwistInclusion hE).app ⊤ (t i))
    (ht : ∀ x ∈ E.support, ∃ i, x ∈
      (hE.toInvertibleSheaf.tensorProduct M).obj.nonvanishingLocus (t i))
    (p : ℙ[k,ι]) (hp : IsClosed ({p} : Set (ℙ[k,ι])))
    (hpre : (M.obj.toProjectiveSpace f v hv) ⁻¹' {p} = (E.support : Set X))
    [IsReduced E.subscheme] (hne : (E.support : Set X).Nonempty) :
    (Scheme.fromSpecResidueField _ p).ker.comap (M.obj.toProjectiveSpace f v hv) = E := by
  let g := M.obj.toProjectiveSpace f v hv
  let F := ((ℙ[k,ι]).fromSpecResidueField p).ker.comap g
  let N := hE.toInvertibleSheaf.tensorProduct M
  let J := ⨆ i, N.zeroIdeal (t i)
  have hF : F.support = E.support := SetLike.coe_injective <| by
    simpa only [F, support_comap, Closeds.coe_preimage,
      Scheme.support_ker_fromSpecResidueField_of_isClosed hp] using hpre
  have hFE : F ≤ E := by
    rw [← (E.isReduced_subscheme_iff_radical_eq).mp inferInstance, ← vanishingIdeal_support, ← hF]
    exact le_support_iff_le_vanishingIdeal.mp le_rfl
  -- Each selected coordinate vanishes at the given point and contributes its zero ideal.
  obtain ⟨e, he⟩ := M.obj.exists_iso_pullbackTwistingSheaf_toProjectiveSpace f v hv
  have hterms (i : ι') : N.zeroIdeal (t i) * E ≤ F := by
    let T : InvertibleSheaf (ℙ[k,ι]) := ⟨Proj.twistingSheaf _ 1, inferInstance⟩
    let s := Proj.polynomialCoordinateSection (R := k) (a i)
    have heq : (T.zeroIdeal s).comap g = M.zeroIdeal (v (a i)) := by
      rw [← T.zeroIdeal_pullbackSections g s, ← he (a i)]
      exact (((InvertibleSheaf.pullback g).obj T).zeroIdeal_hom_app e _).symm
    have hs : p ∈ (T.zeroIdeal s).support := by
      obtain ⟨x, hx⟩ := hne
      have hpx : g x = p := (Set.ext_iff.mp hpre x).2 hx
      have hle : M.zeroIdeal (v (a i)) ≤ E := by
        rw [ha i, M.zeroIdeal_idealTwistInclusion hE]
        exact mul_le_of_le_one_left' le_top
      have hx' : x ∈ ((T.zeroIdeal s).comap g).support := heq ▸ support_antitone hle hx
      rw [support_comap] at hx'
      exact hpx ▸ (show g x ∈ (T.zeroIdeal s).support from hx')
    rw [← M.zeroIdeal_idealTwistInclusion hE, ← ha, ← heq]
    exact comap_mono _ (((T.zeroIdeal s).le_ker_fromSpecResidueField_iff_mem_support hp).mpr hs)
  -- The zero ideals after dividing by the Cartier ideal have no common zero on the fibre.
  have hsup : F ⊔ J = ⊤ := by
    rw [sup_eq_top_iff_disjoint_support, hF]
    dsimp only [J]
    rw [support_iSup, disjoint_iff]
    apply SetLike.coe_injective
    rw [Closeds.coe_inf, Closeds.coe_iInf, Closeds.coe_bot]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x ⟨hx, hJ⟩ ↦ ?_
    obtain ⟨i, hi⟩ := ht x hx
    exact ((N.mem_nonvanishingLocus_iff_notMem_support_zeroIdeal _ _).mp hi)
      (Set.mem_iInter.mp hJ i)
  refine le_antisymm hFE (le_def.mpr fun U ↦ ?_)
  have hJU : J.ideal U * E.ideal U ≤ F.ideal U := by
    dsimp only [J]
    rw [ideal_iSup, iSup_apply, Ideal.iSup_mul]
    exact iSup_le fun i ↦ (le_def.mp (hterms i)) U
  calc
    E.ideal U = (F.ideal U ⊔ J.ideal U) * E.ideal U := by
      rw [← Pi.sup_apply, ← ideal_sup, hsup, ideal_top, Pi.top_apply, Ideal.top_mul]
    _ = F.ideal U * E.ideal U ⊔ J.ideal U * E.ideal U := Ideal.sup_mul _ _ _
    _ ≤ F.ideal U := sup_le Ideal.mul_le_left hJU

end AlgebraicGeometry.Scheme.IdealSheafData
