/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
import QPainleve.AlgebraicGeometry.VectorBundle.SectionZeroLocus
import TauCeti.AlgebraicGeometry.LineBundle.Stalk
import TauCeti.AlgebraicGeometry.Modules.Pullback.ResidueField

/-!
# Zero ideals and nonvanishing loci

The complement of the support of a section's zero ideal is its nonvanishing locus.
Thus a family of sections generates its line bundle exactly when the sum of its
zero ideals is the unit ideal. The pointwise comparison uses the residue-field
fiber criterion for evaluation ideals and the rank-one description of the stalk.
-/

public section

open AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : Scheme.{u}} (L : InvertibleSheaf X)

/-- A section generates the stalk of a line bundle exactly off the support of its zero ideal. -/
@[simp]
theorem compl_support_zeroIdeal (s : Γ(L.obj, ⊤)) :
    (L.zeroIdeal s).support.compl = L.obj.nonvanishingLocus s := by
  ext x
  let M := L.obj
  let R := X.presheaf.stalk x
  let k := X.residueField x
  let m := M.presheaf.germ ⊤ x (Opens.mem_top x) s
  obtain ⟨e'⟩ := M.nonempty_linearEquiv_stalk_of_isInvertible x
  let e := e'.symm
  let d : k ⊗[R] M.presheaf.stalk x ≃ₗ[R] k := (e.lTensor k).trans (TensorProduct.rid R k)
  let b := M.residueFieldPullbackSectionsEquiv x
  have hb : b ((1 : k) ⊗ₜ[R] m) = (X.fromSpecResidueField x).pullbackSections M ⊤ s := by
    dsimp only [b, m, R, k]
    rw [M.residueFieldPullbackSectionsEquiv_tmul_germ, one_smul]
    exact (X.fromSpecResidueField x).pullbackSectionsLE_self M ⊤ s
  have hd : d ((1 : k) ⊗ₜ[R] m) = X.residue x (e m) := by
    dsimp only [d, R, k, e]
    rw [LinearEquiv.trans_apply, LinearEquiv.lTensor_tmul, TensorProduct.rid_tmul,
      Algebra.smul_def, mul_one]
    rfl
  have hs : x ∈ (L.zeroIdeal s).support ↔ X.residue x (e m) = 0 := by
    have h : (X.fromSpecResidueField x).pullbackSections M ⊤ s = 0 ↔
        X.residue x (e m) = 0 := by
      have hzero : b ((1 : k) ⊗ₜ[R] m) = 0 ↔ d ((1 : k) ⊗ₜ[R] m) = 0 :=
        (map_eq_zero_iff b b.injective).trans (map_eq_zero_iff d d.injective).symm
      simp only [hb, hd] at hzero
      exact hzero
    rw [L.zeroIdeal_eq_imageIdealSheaf_evaluation]
    exact (((toFiniteLocallyFree X).obj L).mem_support_imageIdealSheaf_evaluation_section_iff
      s x).trans h
  have hspan : Submodule.span R {m} = ⊤ ↔ IsUnit (e m) := by
    rw [← Submodule.map_eq_top_iff (e := e), Submodule.map_span, Set.image_singleton]
    exact Ideal.span_singleton_eq_top
  -- The open complement has the underlying set complementary to the support.
  change x ∉ (L.zeroIdeal s).support ↔ x ∈ M.nonvanishingLocus s
  rw [hs, M.mem_nonvanishingLocus_iff_of_mem (Opens.mem_top x), hspan]
  exact IsLocalRing.residue_ne_zero_iff_isUnit (e m)

/-- The zero ideals of a family sum to the unit ideal exactly when the nonvanishing
opens of its members cover the scheme. -/
theorem iSup_zeroIdeal_eq_top_iff {ι : Type*} (s : ι → Γ(L.obj, ⊤)) :
    (⨆ i, L.zeroIdeal (s i)) = ⊤ ↔ (⨆ i, L.obj.nonvanishingLocus (s i)) = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_iSup]
  let e := Closeds.complOrderIso X
  rw [← e.injective.eq_iff, e.map_iInf, e.map_bot]
  exact Iff.of_eq (congrArg (· = ⊤) (iSup_congr fun i ↦ L.compl_support_zeroIdeal (s i)))

end TauCeti.AlgebraicGeometry.InvertibleSheaf
