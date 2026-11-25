/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.BoundaryPrimes
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.Integral
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Scheme.LocalSpectrum

/-!
# Boundary primes of a point blowup

The pullback of a boundary containing the center of a point blowup gains one prime
from the exceptional fiber.
-/

public section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The boundary primes after blowing up a closed point on the boundary are the
strict transforms of the original primes and one exceptional prime. The projection
sends each strict-transform prime back to its original prime. -/
theorem exists_equiv_boundaryPrimes_comap_pointBlowup
    {k : Type u} [Field k] [IsNoetherian X] (D : X.IdealSheafData)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    {p : X} (hp : IsClosed ({p} : Set X)) (hD : p ∈ D.support) :
    let I := (X.fromSpecResidueField p).ker
    ∃ e : D.boundaryPrimes ⊕ PUnit.{u + 1} ≃ (D.comap I.blowupToBase).boundaryPrimes,
      (∀ q, I.blowupToBase (e (.inl q)).val = q.val) ∧
      I.blowupToBase (e (.inr PUnit.unit)).val = p := by
  classical
  dsimp only
  let I := (X.fromSpecResidueField p).ker
  let π := I.blowupToBase
  let E := I.comap π
  have := SmoothOfRelativeDimension.smooth 2 f
  have : IsRegular X := IsRegular.of_smooth f
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have hp₂ := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) f hp
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hd
  have : IsIntegral E.subscheme := hE.isIntegral_subscheme
  have : IsNoetherian I.blowup := isNoetherian_of_finiteType π
  let η := E.subschemeι (genericPoint E.subscheme)
  have hI : (I.support : Set X) = {p} := by
    rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hp.closure_eq]
  have hE' (y : I.blowup) (hy : Order.coheight y = 1) : π y = p ↔ y = η := by
    rw [← hE.isEffectiveCartier.mem_support_iff_eq_subschemeι_genericPoint hy, support_comap]
    -- The support of the extended center ideal is the inverse image of the point.
    change π y = p ↔ π y ∈ (I.support : Set X)
    rw [hI, Set.mem_singleton_iff]
  let S := (D.comap π).boundaryPrimes ∩ {y | π y ≠ p}
  have hIso (x : X) (hx : x ≠ p) : x ∈ π.isoLocus :=
    (π.le_isoLocus_iff.mpr I.isIso_blowupToBase_restrict_compl_support)
      (show x ∉ (I.support : Set X) from by rwa [hI, Set.mem_singleton_iff])
  have hη : π η = p := (hE' η hE.isEffectiveCartier.coheight_subschemeι_genericPoint).mpr rfl
  have hηD : η ∈ (D.comap π).boundaryPrimes :=
    mem_boundaryPrimes.mpr ⟨by
      rw [support_comap]
      exact (show π η ∈ D.support from hη.symm ▸ hD),
      hE.isEffectiveCartier.coheight_subschemeι_genericPoint⟩
  have hb : Set.BijOn π S D.boundaryPrimes :=
    bijOn_boundaryPrimes_comap_off_point D π (by rw [hp₂]; norm_num) hIso
  have hdecomp : (D.comap π).boundaryPrimes = insert η S := by
    ext y
    refine ⟨fun hy ↦ ?_, fun hy ↦ (Set.mem_insert_iff.mp hy).elim
      (fun he ↦ he.symm ▸ hηD) (fun hs ↦ hs.1)⟩
    by_cases he : π y = p
    · exact Set.mem_insert_iff.mpr (Or.inl ((hE' y (mem_boundaryPrimes.mp hy).2).mp he))
    · exact Set.mem_insert_of_mem _ ⟨hy, he⟩
  have hηS : η ∉ S := fun h ↦ h.2 hη
  let e := (Equiv.sumCongr hb.equiv.symm (Equiv.refl PUnit)).trans
    ((Equiv.Set.insert hηS).symm.trans (Set.equivOfEq hdecomp.symm))
  refine ⟨e, fun q ↦ ?_, hη⟩
  exact congrArg Subtype.val (hb.equiv.apply_symm_apply q)

/-- A point blowup on the boundary extends a finite labeling of its primes.
The original labels lift to the strict transforms, and the last label denotes
the exceptional prime over the center. -/
theorem exists_equiv_boundaryPrimes_snoc
    {k : Type u} [Field k] [IsNoetherian X] (D : X.IdealSheafData)
    {f : X ⟶ Spec (.of k)} [SmoothOfRelativeDimension 2 f] {m : ℕ}
    {x : X} (hx : IsClosed ({x} : Set X)) (hxD : x ∈ D.support)
    {I : X.IdealSheafData} (hI : (X.fromSpecResidueField x).ker = I)
    (e : Fin m ≃ D.boundaryPrimes) :
    ∃ e' : Fin (m + 1) ≃ (D.comap I.blowupToBase).boundaryPrimes,
      (∀ i, I.blowupToBase (e' i.castSucc).val = (e i).val) ∧
      I.blowupToBase (e' (Fin.last m)).val = x := by
  subst I
  obtain ⟨b, hb, hb₀⟩ := D.exists_equiv_boundaryPrimes_comap_pointBlowup f hx hxD
  let e' := (finSumFinEquiv (m := m) (n := 1)).symm.trans
    ((Equiv.sumCongr e (Equiv.equivPUnit (Fin 1))).trans b)
  refine ⟨e', fun i ↦ ?_, ?_⟩
  · simpa only [e', Equiv.trans_apply, finSumFinEquiv_symm_apply_castSucc,
      Equiv.sumCongr_apply, Sum.map_inl] using hb (e i)
  · have hp : Equiv.equivPUnit (Fin 1) 0 = (PUnit.unit : PUnit.{u + 1}) :=
      Subsingleton.elim _ _
    simpa only [e', Equiv.trans_apply, finSumFinEquiv_symm_last, Equiv.sumCongr_apply,
      Sum.map_inr, hp] using hb₀

/-- The projection of a point blowup distinguishes the boundary primes of the
total transform. The only prime projecting to the center is exceptional. -/
theorem injOn_blowupToBase_boundaryPrimes_comap_pointBlowup
    {k : Type u} [Field k] [IsNoetherian X] (D : X.IdealSheafData)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    {p : X} (hp : IsClosed ({p} : Set X)) (hD : p ∈ D.support) :
    let I := (X.fromSpecResidueField p).ker
    Set.InjOn I.blowupToBase (D.comap I.blowupToBase).boundaryPrimes := by
  dsimp only
  obtain ⟨e, he, hep⟩ := D.exists_equiv_boundaryPrimes_comap_pointBlowup f hp hD
  have hp' := coheight_eq_of_isClosed_of_smoothOfRelativeDimension (n := 2) f hp
  have hne (a : D.boundaryPrimes) : a.val ≠ p := by
    intro h
    have ha := (mem_boundaryPrimes.mp a.property).2
    rw [h, hp'] at ha
    norm_num at ha
  intro x hx y hy
  obtain ⟨a, ha⟩ := e.surjective ⟨x, hx⟩
  obtain ⟨b, hb⟩ := e.surjective ⟨y, hy⟩
  have ha' : (e a).val = x := congrArg Subtype.val ha
  have hb' : (e b).val = y := congrArg Subtype.val hb
  rw [← ha', ← hb']
  intro hxy
  rcases a with a | ⟨⟩ <;> rcases b with b | ⟨⟩
  · rw [he, he] at hxy
    exact congrArg (fun t : D.boundaryPrimes ↦ (e (.inl t)).val) (Subtype.ext hxy)
  · rw [he, hep] at hxy
    exact (hne _ hxy).elim
  · rw [hep, he] at hxy
    exact (hne _ hxy.symm).elim
  · rfl

/-- Blowing up a closed point on a smooth Noetherian surface adds one boundary prime
to the pullback of an ideal sheaf whose support contains the center. -/
theorem encard_boundaryPrimes_comap_pointBlowup
    {k : Type u} [Field k] [IsNoetherian X] (D : X.IdealSheafData)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    {p : X} (hp : IsClosed ({p} : Set X)) (hD : p ∈ D.support) :
    let I := (X.fromSpecResidueField p).ker
    (D.comap I.blowupToBase).boundaryPrimes.encard = D.boundaryPrimes.encard + 1 := by
  obtain ⟨e, -⟩ := D.exists_equiv_boundaryPrimes_comap_pointBlowup f hp hD
  simpa using (ENat.card_congr e).symm

open Classical in
/-- In a point blowup, if the total transform of a boundary is the product of an
effective Cartier divisor and the exceptional ideal, its prime count exceeds
that of the divisor by one exactly when the divisor omits the exceptional curve. -/
theorem ncard_boundaryPrimes_of_totalTransform
    {k : Type u} [Field k] [IsIntegral X] [IsNoetherian X] (D : X.IdealSheafData)
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 f]
    {p : X} (hp : IsClosed ({p} : Set X)) (hpD : p ∈ D.support) (hD : D.IsEffectiveCartier)
    {B : (X.fromSpecResidueField p).ker.blowup.IdealSheafData} (hB : B.IsEffectiveCartier) :
    let I := (X.fromSpecResidueField p).ker
    let π := I.blowupToBase
    let E := I.comap π
    D.comap π = B * E →
    B.boundaryPrimes.ncard + (if E.support ≤ B.support then 0 else 1) =
      D.boundaryPrimes.ncard + 1 := by
  intro I π E h
  have hd := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq f 2).mp inferInstance).2 p hp
  have : Smooth f := SmoothOfRelativeDimension.smooth 2 f
  have := isRegularLocalRing_stalk_of_smooth f p
  let : IsIntegral I.blowup :=
    X.isIntegral_pointBlowup p (fun he ↦ hD.genericPoint_notMem_support (he ▸ hpD))
  let : IsNoetherian I.blowup := isNoetherian_of_finiteType π
  have hE := isExceptionalCurveOfFirstKind_comap_blowupToBase_of_closedPoint p hp hd
  let : IsIntegral E.subscheme := hE.isIntegral_subscheme
  let q := E.subschemeι (genericPoint E.subscheme)
  have hq : Order.coheight q = 1 := hE.isEffectiveCartier.coheight_subschemeι_genericPoint
  have hcard : (D.comap π).boundaryPrimes.ncard = D.boundaryPrimes.ncard + 1 := by
    have hc := congrArg ENat.toNat (D.encard_boundaryPrimes_comap_pointBlowup f hp hpD)
    rw [ENat.toNat_add hD.finite_boundaryPrimes.encard_lt_top.ne
      (show (1 : ℕ∞) ≠ ⊤ by simp), ENat.toNat_one] at hc
    exact hc
  rw [← hcard]
  by_cases hEB : E.support ≤ B.support
  · rw [ite_eq_left hEB, add_zero]
    apply congrArg Set.ncard
    exact boundaryPrimes_eq_of_support_eq (by rw [h, support_mul, sup_eq_left.mpr hEB])
  · have hqB : q ∉ B.boundaryPrimes := by
      intro hb
      apply hEB
      have hs := E.support_eq_closure_subschemeι_genericPoint
      refine IsConcreteLE.le_iff.mpr ?_
      intro x hx
      rw [← SetLike.mem_coe, hs] at hx
      exact (closure_minimal (Set.singleton_subset_iff.mpr (mem_boundaryPrimes.mp hb).1)
        B.support.isClosed) hx
    have hinsert : (D.comap π).boundaryPrimes = insert q B.boundaryPrimes := by
      ext x
      simp only [h, mem_boundaryPrimes, support_mul, Set.mem_insert_iff,
        ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union]
      constructor
      · rintro ⟨hx | hx, hc⟩
        · exact Or.inr ⟨hx, hc⟩
        · exact Or.inl ((hE.isEffectiveCartier.mem_support_iff_eq_subschemeι_genericPoint hc).mp hx)
      · rintro (rfl | ⟨hx, hc⟩)
        · exact ⟨Or.inr (by rw [← range_subschemeι]; exact Set.mem_range_self _), hq⟩
        · exact ⟨Or.inl hx, hc⟩
    rw [ite_eq_right hEB, hinsert, Set.ncard_insert_of_notMem hqB hB.finite_boundaryPrimes]

end AlgebraicGeometry.Scheme.IdealSheafData
