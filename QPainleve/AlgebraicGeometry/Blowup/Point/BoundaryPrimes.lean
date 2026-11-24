/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
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

end AlgebraicGeometry.Scheme.IdealSheafData
