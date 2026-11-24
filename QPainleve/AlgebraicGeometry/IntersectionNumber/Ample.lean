/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.TwistingSheaf
public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.GlobalGeneration.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Power
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Morphisms.Finite
import TauCeti.AlgebraicGeometry.Curves.Normalization

/-!
# Ampleness of globally generated line bundles positive on curves

A globally generated line bundle on a proper scheme over a field is ample if its
degree is positive on each integral closed curve. Its sections define a morphism
to projective space, and positive degree rules out curves in its fibers. This is
the last step of the proof of Nakai–Moishezon in
[Debarre, *Introduction to Mori Theory*, Theorem 4.1](https://www.math.ens.psl.eu/~debarre/M2.pdf).
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper morphism is finite if the pullback of a line-bundle class has positive
degree on every integral closed curve. -/
theorem isFinite_of_intersectionNumber_pullback_pos
    {k : Type u} [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [CompactSpace Y] (f : X ⟶ Y) [IsProper f]
    (a : LineBundleClass Y)
    (ha : ∀ {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
      (i : C ⟶ X) [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ X ↘ Spec (.of k) →
        0 < LineBundleClass.intersectionNumber k i (LineBundleClass.pullback f a)) :
    IsFinite f := by
  by_contra hfin
  obtain ⟨y, hy, C, i, hi, hC, hdim⟩ := f.exists_closed_curve_in_fiber_of_not_isFinite hfin
  have : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have : IsClosedImmersion (f.fiberι y) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Y.fromSpecResidueField y)))
  let j := i ≫ f.fiberι y
  let : C.Over (Spec (.of k)) := ⟨j ≫ X ↘ Spec (.of k)⟩
  have : C.IsCurveOver k := Scheme.isCurveOver_iff.mpr
    ⟨hC, inferInstanceAs (IsProper (j ≫ X ↘ Spec (.of k))), hdim⟩
  have hp := ha j rfl
  rw [LineBundleClass.intersectionNumber_pullback] at hp
  exact hp.ne' (LineBundleClass.intersectionNumber_eq_zero_of_eq_comp k _
    (i ≫ f.fiberToSpecResidueField y) (Y.fromSpecResidueField y)
    (by simp only [j, Category.assoc, f.fiber_fac y])
    (t := IsLocalRing.closedPoint (Y.residueField y))
    (fun z ↦ (Subsingleton.elim z _) ▸ specializes_rfl) _)

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Generating sections of a line bundle that has positive degree on every integral closed
curve give a finite morphism to projective space, with the original class as the pullback
of the hyperplane class. -/
theorem exists_finite_toProjectiveSpace_of_intersectionNumber_pos
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (L : InvertibleSheaf X) {ι : Type u} [Finite ι]
    (s : ι → Γ(L.obj, ⊤)) (hcover : (⨆ i, L.obj.nonvanishingLocus (s i)) = ⊤)
    (hpos : ∀ {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
      (i : C ⟶ X) [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ X ↘ Spec (.of k) →
        0 < LineBundleClass.intersectionNumber k i (LineBundleClass.mk L)) :
    let A := MvPolynomial.homogeneousSubmodule ι k
    let H : InvertibleSheaf (Proj A) := ⟨Proj.twistingSheaf A 1, inferInstance⟩
    ∃ p : X ⟶ Proj A, p ≫ Proj.toSpecCoeff A = X ↘ Spec (.of k) ∧ IsFinite p ∧
      LineBundleClass.pullback p (LineBundleClass.mk H) = LineBundleClass.mk L := by
  intro A H
  let f := X ↘ Spec (.of k)
  let p := L.obj.toProjectiveSpace f s hcover
  let q := Proj.toSpecCoeff A
  have : IsProper q := by
    dsimp only [q, A]
    rw [← Proj.over_polynomial]
    infer_instance
  have hcomp : p ≫ q = f := L.obj.toProjectiveSpace_toSpecCoeff f s hcover
  have : IsProper (p ≫ q) := hcomp.symm ▸ ‹IsProper f›
  have : IsProper p := .of_comp p q
  have : CompactSpace (Proj A) := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨e, -⟩ := L.obj.exists_iso_pullbackTwistingSheaf_toProjectiveSpace f s hcover
  have hclass : LineBundleClass.pullback p (LineBundleClass.mk H) = LineBundleClass.mk L := by
    rw [LineBundleClass.pullback_mk]
    exact LineBundleClass.mk_eq_mk_iff.mpr ⟨
      eqToIso (InvertibleSheaf.pullback_obj_obj p H) ≪≫ e⟩
  refine ⟨p, hcomp, p.isFinite_of_intersectionNumber_pullback_pos (k := k)
    (LineBundleClass.mk H) ?_, hclass⟩
  intro C _ _ i _ hi
  rw [hclass]
  exact hpos i hi

/-- A globally generated line bundle on a proper scheme over a field is ample if
its intersection number with every integral closed curve is positive. -/
theorem isAmple_of_isGloballyGenerated_of_intersectionNumber_pos
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] {L : InvertibleSheaf X} (hL : L.IsGloballyGenerated)
    (hpos : ∀ {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
      (i : C ⟶ X) [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ X ↘ Spec (.of k) →
        0 < LineBundleClass.intersectionNumber k i (LineBundleClass.mk L)) :
    (LineBundleClass.mk L).IsAmple := by
  classical
  let f := X ↘ Spec (.of k)
  let U (s : Γ(L.obj, ⊤)) := L.obj.nonvanishingLocus s
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hc : IsCompactElement (⊤ : X.Opens) := (Opens.isCompactElement_iff _).mpr isCompact_univ
  obtain ⟨T, hT⟩ := (isCompactElement_iff_exists_le_iSup_of_le_iSup _).mp hc _ U
    (isGloballyGenerated_iff_iSup_nonvanishingLocus_eq_top.mp hL).ge
  have hcover : (⨆ s : T, U s) = ⊤ := top_le_iff.mp (by
    simpa only [iSup_subtype, Finset.sup_eq_iSup] using hT)
  obtain ⟨p, -, hp, hclass⟩ := L.exists_finite_toProjectiveSpace_of_intersectionNumber_pos
    Subtype.val hcover hpos
  let A := MvPolynomial.homogeneousSubmodule (↑T) k
  have : IsProper (Proj.toSpecCoeff A) := by
    rw [← Proj.over_polynomial]
    infer_instance
  have : CompactSpace (Proj A) := QuasiCompact.compactSpace_of_compactSpace (Proj.toSpecCoeff A)
  let M : InvertibleSheaf (Proj A) := ⟨Proj.twistingSheaf _ 1, inferInstance⟩
  have hM : (LineBundleClass.mk M).IsAmple :=
    Proj.isAmple_twistingSheaf (fun s : T ↦ MvPolynomial.X s)
      (fun s ↦ (MvPolynomial.mem_homogeneousSubmodule ..).mpr (MvPolynomial.isHomogeneous_X k s))
      (Proj.iSup_basicOpen_eq_top _ _ (MvPolynomial.irrelevant_eq_span_X _ _).le) Nat.one_pos
  have hclass' : LineBundleClass.pullback p (LineBundleClass.mk M) = LineBundleClass.mk L := hclass
  exact hclass' ▸ hM.pullback_of_isAffineHom p

/-- A line bundle with a globally generated positive tensor power is ample if
its intersection number with every integral closed curve is positive. -/
theorem isAmple_of_isGloballyGenerated_tensorPow_of_intersectionNumber_pos
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] {L : InvertibleSheaf X} {n : ℕ} (hn : 0 < n)
    (hL : (L.tensorPow n).IsGloballyGenerated)
    (hpos : ∀ {C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]
      (i : C ⟶ X) [IsClosedImmersion i], C ↘ Spec (.of k) = i ≫ X ↘ Spec (.of k) →
        0 < LineBundleClass.intersectionNumber k i (LineBundleClass.mk L)) :
    (LineBundleClass.mk L).IsAmple := by
  apply LineBundleClass.IsAmple.of_pow hn
  rw [← LineBundleClass.mk_tensorPow]
  apply isAmple_of_isGloballyGenerated_of_intersectionNumber_pos (k := k) hL
  intro C _ _ i _ hi
  have : RelativeDimensionLE 1 (C ↘ Spec (.of k)) :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  rw [LineBundleClass.mk_tensorPow, LineBundleClass.intersectionNumber_pow_of_isIntegral]
  exact mul_pos (Int.natCast_pos.mpr hn) (hpos i hi)

end TauCeti.AlgebraicGeometry.InvertibleSheaf
