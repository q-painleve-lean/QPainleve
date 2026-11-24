/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.Nef.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Automorphism

import QPainleve.AlgebraicGeometry.Chow.Nef.Boundary
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Orientation
import TauCeti.FieldTheory.IsSepClosed

/-!
# The orientation-preserving Picard kernel of a nef square-zero pair

For a numbered nef square-zero nodal boundary, an automorphism of the pair over the field
acting trivially on the Picard group fixes the prime components. In the
orientation-preserving subgroup it also fixes each branch. This gives a
membership criterion for the Picard kernel that uses the orientation sign.
-/

public section

open CategoryTheory DihedralGroup TauCeti.AlgebraicGeometry LineBundleClass

universe u v

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  {ι : Type v} {marks : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}
  {n : ℕ} [NeZero n]

local notation "S" => Spec (CommRingCat.of k)
local notation "s" => X ↘ S
local notation "C" => D.subscheme
local notation "classOf(" h ")" => (LineBundleClass.mk (toInvertibleSheaf h))⁻¹

/-- For a nef square-zero nodal cycle, an automorphism of the pair over the field
belongs to the Picard kernel with fixed components and branches exactly when it
acts trivially on the Picard group and preserves the cycle orientation. -/
theorem mem_picardNodalBoundaryAut_iff_preserves_orientation
    (hD : D.IsEffectiveCartier) (a : Aut X) (ha : a.asIso.hom ≫ s = s)
    (d : C ≅ C) (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ a.asIso.hom)
    (numbering : Scheme.NodalCycleNumbering marks n)
    (hnef : classOf(hD).IsNef k s)
    (hsq : Chow.classIntersectionNumber k X classOf(hD) classOf(hD) = 0) :
    let hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s) := by
      rw [← D.over_eq_subschemeι_comp]
      exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
    letI : d.hom.IsOver S := ⟨by rw [D.over_eq_subschemeι_comp, reassoc_of% hd, ha]⟩
    a ∈ D.picardNodalBoundaryAut hN ↔
      (∀ L, pullback a.asIso.hom L = L) ∧
        cycleOrientationSign (d.boundaryCycleAction numbering numbering) = 1 := by
  intro hN
  have : d.hom.IsOver S := ⟨by rw [D.over_eq_subschemeι_comp, reassoc_of% hd, ha]⟩
  have hbranches : d.FixesNodalBranches (D.subschemeι ≫ s) hN
      (by rw [reassoc_of% hd, ha]) ↔ d.boundaryCycleAction numbering numbering = 1 := by
    refine (Iso.fixesNodalBranches_iff_of_comm
      (hD := PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := C ↘ S))
      (hd := HomIsOver.comp_over (f := d.hom)) (Iso.refl C)
      (by simpa only [Iso.refl_hom, Category.id_comp] using D.over_eq_subschemeι_comp)
      (by rw [Iso.trans_refl, Iso.refl_trans])).trans ?_
    exact d.fixesNodalBranches_iff_boundaryCycleAction_eq_one numbering
  constructor
  · intro hm
    obtain ⟨_, hPic, _, _⟩ := (D.mem_picardNodalBoundaryAut hN).mp hm
    have hfix := D.fixesNodalBranches_of_mem_picardNodalBoundaryAut hN ha hm d hd
    exact ⟨hPic, by rw [hbranches.mp hfix, map_one]⟩
  · rintro ⟨hPic, horient⟩
    have : IsNoetherian X := isNoetherian_of_finiteType s
    have : ConnectedSpace C :=
      GeometricallyConnected.connectedSpace_of_subsingleton (f := C ↘ S)
    have hconn : _root_.IsPreconnected (D.support : Set X) := by
      rw [← D.range_subschemeι]
      exact (isConnected_range D.subschemeι.continuous).isPreconnected
    have hpb : IsPullback D.subschemeι d.hom a.asIso.hom D.subschemeι :=
      .of_vert_isIso ⟨hd.symm⟩
    have hmap : D.comap a.asIso.hom = D := by
      simpa only [ker_subschemeι] using (ker_eq_comap_of_isPullback D.subschemeι hpb).symm
    have hfix := hD.fixes_boundary_components_of_picard_trivial hconn hnef hsq a.asIso hmap hPic
    refine (D.mem_picardNodalBoundaryAut hN).mpr ⟨ha, hPic, hfix, d, hd, hbranches.mpr ?_⟩
    exact hD.boundaryCycleAction_eq_one_of_fixes_components a.asIso d hd numbering hfix horient

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
