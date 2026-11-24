/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.Nef
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import QPainleve.AlgebraicGeometry.LineBundle.GlobalGeneration
import TauCeti.AlgebraicGeometry.Cohomology.Pullback
import TauCeti.AlgebraicGeometry.Curves.Normalization
import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections
import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Pullback
import TauCeti.AlgebraicGeometry.LineBundle.SectionDegree

/-!
# Nefness from globally generated line bundles

A globally generated line bundle restricts to a line bundle with a nonzero section on every
integral curve. In particular, sufficiently high ample twists of any line bundle are nef.
Over an algebraically closed field, restriction to a curve of degree zero kills a nonzero
section whenever the space of global sections has dimension greater than one.
-/

public section

open AlgebraicGeometry CategoryTheory Filter
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry

/-- A globally generated line bundle has nonnegative degree on every proper integral curve. -/
theorem InvertibleSheaf.IsGloballyGenerated.isNef {k : Type u} [Field k] {X : Scheme.{u}}
    {L : InvertibleSheaf X} (hL : L.IsGloballyGenerated) (f : X ⟶ Spec (.of k)) :
    (LineBundleClass.mk L).IsNef k f := by
  refine (LineBundleClass.isNef_iff k f _).mpr fun C _ _ i _ _ ↦ ?_
  have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  let M := (InvertibleSheaf.pullback i).obj L
  have hM : M.IsGloballyGenerated := hL.pullback i
  obtain ⟨s, hs⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp hM (genericPoint C)
  have hs₀ : s ≠ 0 := by
    intro h
    simp [h, Scheme.Modules.nonvanishingLocus_zero] at hs
  rw [LineBundleClass.intersectionNumber_def, LineBundleClass.pullback_mk,
    LineBundleClass.eulerDegree_mk]
  exact M.eulerDegree_nonneg_of_ne_zero k s hs₀

open LineBundleClass in
/-- Over an algebraically closed field, if a line bundle has at least two independent
global sections and degree zero on a proper integral curve, some nonzero global section
pulls back to zero on the curve. -/
theorem InvertibleSheaf.exists_nonzero_section_of_intersectionNumber_eq_zero
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] (L : InvertibleSheaf X)
    (hnum : 1 < Module.finrank k Γ(L.obj, ⊤))
    {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
    (i : C ⟶ X) [i.IsOver (Spec (.of k))]
    (hdeg : intersectionNumber k i (LineBundleClass.mk L) = 0) :
    ∃ s : Γ(L.obj, ⊤), s ≠ 0 ∧ i.pullbackSections L.obj ⊤ s = 0 := by
  let M := (InvertibleSheaf.pullback i).obj L
  have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  by_cases hvan : ∀ s : Γ(L.obj, ⊤), i.pullbackSections L.obj ⊤ s = 0
  · have : Nontrivial Γ(L.obj, ⊤) := Module.nontrivial_of_finrank_pos (Nat.zero_lt_one.trans hnum)
    obtain ⟨s, hs⟩ := exists_ne (0 : Γ(L.obj, ⊤))
    exact ⟨s, hs, hvan s⟩
  obtain ⟨s, hs⟩ := not_forall.mp hvan
  have hM : LineBundleClass.mk M = 1 :=
    (M.eulerDegree_eq_zero_iff_of_ne_zero k _ hs).mp (by
      rwa [intersectionNumber_def, pullback_mk, eulerDegree_mk] at hdeg)
  obtain ⟨e⟩ := mk_eq_mk_iff.mp (hM.trans (mk_trivial (X := C)).symm)
  have hconst := C.baseRingToGlobalSections_bijective_of_isIntegrallyClosedIn k
    isIntegrallyClosedIn_of_isAlgClosed
  have hdim : Module.finrank k (Cohomology M.obj 0) = 1 := by
    rw [(cohomologyBaseLinearEquivOfIso k e 0).finrank_eq]
    exact finrank_cohomology_zero_trivial_eq_one_of_surjective k hconst.surjective
  have hbase (a : k) : i.appTop (baseRingToGlobalSections k X a) =
      baseRingToGlobalSections k C a := by
    rw [baseRingToGlobalSections_apply, baseRingToGlobalSections_apply,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, HomIsOver.comp_over]
  let r : Cohomology L.obj 0 →ₗ[k] Cohomology M.obj 0 :=
    { toFun := i.cohomologyPullback L.obj 0
      map_add' := map_add _
      map_smul' := fun a x ↦ by
        rw [base_smul_cohomology, i.cohomologyPullback_smul, hbase, RingHom.id_apply]
        exact (base_smul_cohomology k C ((Scheme.Modules.pullback i).obj L.obj) 0 a _).symm }
  have : Module.Finite k (Cohomology M.obj 0) := Module.finite_of_finrank_pos (hdim ▸ zero_lt_one)
  have hnoninj : ¬ Function.Injective r := fun hr ↦ by
    have hle := LinearMap.finrank_le_finrank_of_injective hr
    rw [finrank_cohomology_zero_eq_finrank_globalSections, hdim] at hle
    exact hnum.not_ge hle
  obtain ⟨x, hx, hx₀⟩ := (r.ker.ne_bot_iff).mp (mt LinearMap.ker_eq_bot.mp hnoninj)
  have hz : i.cohomologyPullback L.obj 0 x = 0 := hx
  let s := cohomologyZeroEquiv L.obj x
  refine ⟨s, fun h ↦ hx₀ ((cohomologyZeroEquiv L.obj).injective (h.trans (map_zero _).symm)), ?_⟩
  rw [← i.cohomologyZeroEquiv_cohomologyPullback, hz, map_zero]
  rfl

/-- Twisting a line-bundle class by every sufficiently high power of an ample class makes it
nef. -/
theorem LineBundleClass.IsAmple.eventually_isNef_mul_pow {k : Type u} [Field k]
    {X : Scheme.{u}} {a : LineBundleClass X} (ha : a.IsAmple) (b : LineBundleClass X)
    (f : X ⟶ Spec (.of k)) :
    ∀ᶠ n : ℕ in atTop, (b * a ^ n).IsNef k f := by
  obtain ⟨L, rfl⟩ := LineBundleClass.mk_surjective a
  obtain ⟨M, rfl⟩ := LineBundleClass.mk_surjective b
  filter_upwards [M.obj.eventually_exists_generatingSections_tensor_tensorPow_of_isAmple L ha]
    with n ⟨s, _⟩
  let P := M.tensorProduct (L.tensorPow n)
  have hP : P.IsGloballyGenerated :=
    InvertibleSheaf.isGloballyGenerated_iff_nonempty_generatingSections.mpr
      ⟨s.equivOfIso (M.tensorProductObjIso (L.tensorPow n)).symm⟩
  simpa only [P, LineBundleClass.mk_tensorProduct, LineBundleClass.mk_tensorPow] using hP.isNef f

end TauCeti.AlgebraicGeometry
