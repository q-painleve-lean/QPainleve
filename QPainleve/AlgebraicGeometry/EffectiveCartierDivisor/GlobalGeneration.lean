/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import Mathlib.Order.OrderIsoNat
import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
import QPainleve.AlgebraicGeometry.Cohomology.CartierPairing
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Cohomology.SerreVanishing
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Twist
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import QPainleve.AlgebraicGeometry.LineBundle.Power
import QPainleve.AlgebraicGeometry.LineBundle.Pullback
import QPainleve.AlgebraicGeometry.LineBundle.TensorProduct

/-!
# Global generation from an ample Cartier restriction

For an effective Cartier divisor on a projective scheme over a field, ampleness of its
associated line bundle on the divisor implies global generation of all sufficiently high
powers on the ambient scheme. Serre vanishing on the divisor makes the transition maps on
first cohomology eventually surjective. Their finite dimensions stabilize, so the maps
become injective as well and sections on the divisor lift to the ambient scheme.

This is the section-lifting step of the Nakai–Moishezon criterion in O. Debarre,
*Introduction to Mori Theory*, Theorem 4.1.
-/

public noncomputable section

open CategoryTheory MonoidalCategory Filter TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {X : Scheme.{u}} {I : X.IdealSheafData}

private theorem eventually_subsingleton_cohomology_quotient (k : Type u) [Field k]
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    (L : InvertibleSheaf X)
    (hA : (LineBundleClass.pullback I.subschemeι (LineBundleClass.mk L)).IsAmple) :
    ∀ᶠ n : ℕ in atTop,
      Subsingleton (Cohomology ((L.tensorPow n).obj ⊗ I.pushforwardSubscheme) 1) := by
  let i := I.subschemeι
  let M := (InvertibleSheaf.pullback i).obj L
  have : I.subscheme.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k i
  have hM : (LineBundleClass.mk M).IsAmple := by
    simpa only [M, i, LineBundleClass.pullback_mk] using hA
  let f := I.subscheme ↘ Spec (.of k)
  filter_upwards [f.eventually_subsingleton_cohomology_tensorPow_of_isAmple (𝟙_ _) M hM]
    with n hn
  let e := (L.nonempty_pullback_tensorPow_iso i n).some
  let e' := eqToIso (InvertibleSheaf.pullback_obj_obj i (L.tensorPow n)).symm ≪≫
    e ≪≫ (λ_ (M.tensorPow n).obj).symm
  have := hn 1 Nat.one_pos
  exact ((I.cohomologyTensorRestrictionEquiv k (L.tensorPow n) 1).trans
    (cohomologyBaseLinearEquivOfIso k e' 1)).injective.subsingleton

private theorem eventually_injective_cohomologyMap_tensorIdeal (k : Type u) [Field k]
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] (hI : I.IsEffectiveCartier)
    (hA : (LineBundleClass.pullback I.subschemeι
      (LineBundleClass.mk hI.toInvertibleSheaf.dual)).IsAmple) :
    ∀ᶠ n : ℕ in atTop, Function.Injective
      (cohomologyMap ((hI.toInvertibleSheaf.dual.tensorPow (n + 1)).obj ◁ I.sheafι) 1) := by
  let L := hI.toInvertibleSheaf.dual
  let d (n : ℕ) := Module.finrank k (Cohomology (L.tensorPow n).obj 1)
  let a (n : ℕ) := (L.tensorPow (n + 1)).obj
  let src (n : ℕ) := cohomologyBaseLinearEquivOfIso k (hI.tensorPowSuccIdealIso n).symm 1
  let tgt (n : ℕ) := cohomologyBaseLinearEquivOfIso k (ρ_ (a n)) 1
  let map (n : ℕ) := (tgt n).toLinearMap.comp
    ((cohomologyMapBaseLinear k X (a n ◁ I.sheafι) 1).comp (src n).toLinearMap)
  have hmaps : ∀ᶠ n : ℕ in atTop, Function.Surjective (map n) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_subsingleton_cohomology_quotient k L hA)
    filter_upwards [eventually_ge_atTop N] with n hn
    have : Subsingleton (Cohomology (a n ⊗ I.pushforwardSubscheme) 1) :=
      hN (n + 1) (hn.trans (Nat.le_succ n))
    have hS := I.shortExact_tensor_toPushforwardSubscheme (a n)
    have hs : Function.Surjective (cohomologyMap (a n ◁ I.sheafι) 1) :=
      fun y ↦ by
        have hy : cohomologyMap (a n ◁ I.toPushforwardSubscheme) 1 y = 0 :=
          Subsingleton.elim _ _
        exact (exact_cohomologyMap_cohomologyMap hS 1 y).mp hy
    simpa only [map, LinearMap.coe_comp, LinearEquiv.coe_coe, coe_cohomologyMapBaseLinear] using
      (tgt n).surjective.comp (hs.comp (src n).surjective)
  have hfinite (n : ℕ) : Module.Finite k (Cohomology (L.tensorPow n).obj 1) :=
    moduleFinite_cohomology_of_isProjectiveOver k _ _
  have hstep : ∀ᶠ n : ℕ in atTop, d (n + 1) ≤ d n := hmaps.mono fun n hn ↦ by
    have := hfinite n
    exact LinearMap.finrank_le_finrank_of_surjective hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
  have hanti : Antitone (fun n ↦ d (N + n)) := antitone_nat_of_succ_le fun n ↦
    hN (N + n) (Nat.le_add_right ..)
  obtain ⟨m, hm⟩ := WellFoundedLT.antitone_chain_condition hanti
  filter_upwards [hmaps, eventually_ge_atTop (N + m)] with n hn hnm
  have := hfinite n
  have := hfinite (n + 1)
  have heq : d n = d (n + 1) := by
    have h := (hm (n - N) (by omega)).symm.trans (hm (n + 1 - N) (by omega))
    simpa only [Nat.add_sub_of_le (by omega : N ≤ n),
      Nat.add_sub_of_le (by omega : N ≤ n + 1)] using h
  have hinj := (OrzechProperty.bijective_of_surjective_of_finrank_le (map n) hn heq.le).injective
  simp only [map, LinearMap.coe_comp, LinearEquiv.coe_coe, coe_cohomologyMapBaseLinear] at hinj
  -- Reassociate the three functions to cancel the source isomorphism first.
  rw [← Function.comp_assoc] at hinj
  exact (hinj.of_comp_right (src n).surjective).of_comp

/-- If the associated line bundle of an effective Cartier divisor is ample on the divisor,
all global sections on the divisor of sufficiently high powers lift to the ambient scheme. -/
theorem eventually_surjective_pullbackSectionsLE_of_isAmple (k : Type u) [Field k]
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] (hI : I.IsEffectiveCartier)
    (hA : (LineBundleClass.pullback I.subschemeι
      (LineBundleClass.mk hI.toInvertibleSheaf.dual)).IsAmple) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective
      (I.subschemeι.pullbackSectionsLE ((hI.toInvertibleSheaf.dual.tensorPow n).obj) ⊤ ⊤
        (by rw [Scheme.Hom.preimage_top])) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hI.eventually_injective_cohomologyMap_tensorIdeal k hA)
  refine eventually_atTop.mpr ⟨N + 1, fun n hn ↦ ?_⟩
  cases n with
  | zero => omega
  | succ n =>
    let M := hI.toInvertibleSheaf.dual.tensorPow (n + 1)
    let i := I.subschemeι
    have hS := I.shortExact_tensor_toPushforwardSubscheme M.obj
    have hinj := hN n (by omega)
    have hsurj : Function.Surjective (cohomologyMap (M.obj ◁ I.toPushforwardSubscheme) 0) := by
      intro y
      apply (exact_cohomologyMap_cohomologyδ hS 0 1 rfl y).mp
      apply hinj
      rw [map_zero]
      exact (exact_cohomologyδ_cohomologyMap hS 0 1 rfl _).mpr ⟨y, rfl⟩
    have happ : Function.Surjective ⇑((M.obj ◁ I.toPushforwardSubscheme).app ⊤) := by
      intro y
      obtain ⟨x, hx⟩ := hsurj ((cohomologyZeroEquiv _).symm y)
      exact ⟨cohomologyZeroEquiv _ x, by rw [← cohomologyZeroEquiv_cohomologyMap, hx,
        AddEquiv.apply_symm_apply]⟩
    have := I.isIso_tensorRestrictionHom M
    have hunit : Function.Surjective
        (((pullbackPushforwardAdjunction i).unit.app M.obj).app ⊤) := by
      rw [← I.tensorRestrictionHom_unit M]
      exact (ConcreteCategory.bijective_of_isIso ((I.tensorRestrictionHom M).app ⊤)).surjective.comp
        (happ.comp (ConcreteCategory.bijective_of_isIso ((ρ_ M.obj).inv.app ⊤)).surjective)
    let topLE : (⊤ : I.subscheme.Opens) ≤ i ⁻¹ᵁ ⊤ := by rw [Scheme.Hom.preimage_top]
    have : IsIso (homOfLE topLE) := isIso_homOfLE (Scheme.Hom.preimage_top i).symm
    have htop := (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.pullback i).obj M.obj).presheaf.map (homOfLE topLE).op)).surjective
    intro t
    obtain ⟨x, hx⟩ := (htop.comp hunit) t
    refine ⟨x, ?_⟩
    rw [Scheme.Hom.pullbackSectionsLE_apply, Scheme.Hom.pullbackSections_apply]
    exact hx

/-- If `𝒪_X(D)|_D` is ample for an effective Cartier divisor `D` on a projective scheme,
every sufficiently high tensor power of `𝒪_X(D)` is globally generated. -/
theorem eventually_isGloballyGenerated_of_isAmple (k : Type u) [Field k]
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] (hI : I.IsEffectiveCartier)
    (hA : (LineBundleClass.pullback I.subschemeι
      (LineBundleClass.mk hI.toInvertibleSheaf.dual)).IsAmple) :
    ∀ᶠ n : ℕ in atTop, (hI.toInvertibleSheaf.dual.tensorPow n).IsGloballyGenerated := by
  let L := hI.toInvertibleSheaf.dual
  let i := I.subschemeι
  let M := (InvertibleSheaf.pullback i).obj L
  have hM : (LineBundleClass.mk M).IsAmple := by
    simpa only [M, i, L, LineBundleClass.pullback_mk] using hA
  obtain ⟨s, hs⟩ := hI.exists_zeroIdeal_eq_dual
  have hsections := eventually_exists_generatingSections_tensor_tensorPow_of_isAmple (𝟙_ _) M hM
  filter_upwards [hsections,
    hI.eventually_surjective_pullbackSectionsLE_of_isAmple k hA,
    eventually_gt_atTop 0] with n ⟨g, _⟩ hlift hn
  let P := L.tensorPow n
  have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X P.obj := P.property
  have : TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L.obj := L.property
  let e := eqToIso (InvertibleSheaf.pullback_obj_obj i P).symm
  let eP := (L.nonempty_pullback_tensorPow_iso i n).some ≪≫ (λ_ (M.tensorPow n).obj).symm
  have hgen : ((InvertibleSheaf.pullback i).obj P).IsGloballyGenerated :=
    InvertibleSheaf.isGloballyGenerated_iff_nonempty_generatingSections.mpr
      ⟨g.equivOfIso eP.symm⟩
  refine InvertibleSheaf.isGloballyGenerated_iff.mpr fun x ↦ ?_
  by_cases hx : x ∈ I.support
  · have hx' : x ∈ (I.support : Set X) := hx
    rw [← I.range_subschemeι] at hx'
    obtain ⟨y, hy⟩ := hx'
    obtain ⟨t, ht⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp hgen y
    obtain ⟨v, hv⟩ := hlift (e.symm.hom.app ⊤ t)
    refine ⟨v, ?_⟩
    rw [← nonvanishingLocus_hom_app e.symm, ← hv, nonvanishingLocus_pullbackSectionsLE,
      top_inf_eq] at ht
    exact hy ▸ i.mem_preimage.mp ht
  · let p := L.tensorPowObjIso n
    refine ⟨p.symm.hom.app ⊤ (tensorPowSection s n), ?_⟩
    rw [nonvanishingLocus_hom_app p.symm, nonvanishingLocus_tensorPowSection s hn,
      L.mem_nonvanishingLocus_iff_notMem_support_zeroIdeal, hs]
    exact hx

/-- Twisting sections by a positive power of the defining section of an effective Cartier
divisor removes its support from each nonvanishing locus and preserves affineness of these
loci. -/
theorem exists_twisted_sections
    (hI : I.IsEffectiveCartier) (L : InvertibleSheaf X)
    {ι : Type u} (t : ι → Γ(L.obj, ⊤))
    (ht : ∀ i, IsAffineOpen (L.obj.nonvanishingLocus (t i))) {n : ℕ} (hn : 0 < n) :
    let M := L.tensorProduct (InvertibleSheaf.tensorPow hI.toInvertibleSheaf.dual n)
    ∃ s : ι → Γ(M.obj, ⊤), ∀ i,
      (∀ x : X, x ∈ M.obj.nonvanishingLocus (s i) ↔
          x ∈ L.obj.nonvanishingLocus (t i) ∧ x ∉ I.support) ∧
        IsAffineOpen (M.obj.nonvanishingLocus (s i)) := by
  intro M
  let D : InvertibleSheaf X := hI.toInvertibleSheaf.dual
  obtain ⟨d, hd⟩ := hI.exists_zeroIdeal_eq_dual
  have hd' : D.zeroIdeal d = I := hd
  let a := (D.tensorPowObjIso n).symm
  let b := (L.tensorProductObjIso (D.tensorPow n)).symm
  let d' := a.hom.app ⊤ (tensorPowSection d n)
  refine ⟨fun i ↦ b.hom.app ⊤ (tmulRight L.obj d' (t i)), fun i ↦ ?_⟩
  dsimp only [d']
  rw [nonvanishingLocus_hom_app, nonvanishingLocus_tmulRight,
    nonvanishingLocus_hom_app, nonvanishingLocus_tensorPowSection _ hn]
  constructor
  · intro x
    exact and_congr_right fun _ ↦ by
      exact (D.mem_nonvanishingLocus_iff_notMem_support_zeroIdeal d x).trans
        (by rw [hd'])
  · rw [← nonvanishingLocus_map (L.obj.nonvanishingLocus (t i)).leTop]
    exact (ht i).nonvanishingLocus _

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
