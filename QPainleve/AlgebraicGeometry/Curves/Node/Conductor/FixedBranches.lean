/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Isomorphism
public import TauCeti.AlgebraicGeometry.Curves.Node.Normalization

import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.Pullback.Carrier
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Fixed branches of a nodal curve

Two disjoint open sets approaching a node distinguish its two branches.
An automorphism that fixes the node and preserves the two open sets fixes
the branches separately. This applies to the attachment of a strict transform
to the exceptional curve of a nodal blowup.
-/

public section

open AlgebraicGeometry TopologicalSpace TauCeti TauCeti.AlgebraicGeometry

namespace CategoryTheory.Iso

universe u

section

variable {k : Type u} [Field k] {C : Scheme.{u}} (a : C ≅ C)
  (f : C ⟶ Spec (.of k)) (hN : AtWorstNodalOfRelativeDimensionOne f) (ha : a.hom ≫ f = f)

/-- Pointwise fixation of the normalization points over the nodes. Over a separably closed
field this fixes both branches of each node individually, including at self-nodes. -/
def FixesNodalBranches : Prop :=
  letI : C.Over (Spec (.of k)) := ⟨f⟩
  letI : a.hom.IsOver (Spec (.of k)) := ⟨ha⟩
  letI : SyntomicOfRelativeDimension 1 (C ↘ Spec (.of k)) := hN.syntomic
  ∀ y : (C.singularLocus k).blowup,
    (C.singularLocus k).blowupToBase y ∈ (C.singularLocus k).support →
      (a.singularLocusBlowupIso (R := k)).hom y = y

/-- The normalization-point criterion for branch fixation. -/
theorem fixesNodalBranches_iff :
    a.FixesNodalBranches f hN ha ↔
      letI : C.Over (Spec (.of k)) := ⟨f⟩
      letI : a.hom.IsOver (Spec (.of k)) := ⟨ha⟩
      letI : SyntomicOfRelativeDimension 1 (C ↘ Spec (.of k)) := hN.syntomic
      ∀ y : (C.singularLocus k).blowup,
        (C.singularLocus k).blowupToBase y ∈ (C.singularLocus k).support →
          (a.singularLocusBlowupIso (R := k)).hom y = y :=
  Iff.rfl

/-- Branch fixation is the pointwise identity on the branch scheme. -/
theorem fixesNodalBranches_iff_branchScheme :
    a.FixesNodalBranches f hN ha ↔
      letI : C.Over (Spec (.of k)) := ⟨f⟩
      letI : a.hom.IsOver (Spec (.of k)) := ⟨ha⟩
      letI : SyntomicOfRelativeDimension 1 (C ↘ Spec (.of k)) := hN.syntomic
      ∀ q : C.branchScheme k, (a.branchSchemeIso (R := k)).hom q = q := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : a.hom.IsOver (Spec (.of k)) := ⟨ha⟩
  have : SyntomicOfRelativeDimension 1 (C ↘ Spec (.of k)) := hN.syntomic
  let i := C.branchSchemeToBlowup k
  let p := C.isPullback_branchScheme k
  have : IsClosedImmersion i := MorphismProperty.of_isPullback p inferInstance
  have hRange : Set.range i =
      (C.singularLocus k).blowupToBase ⁻¹' ((C.singularLocus k).support : Set C) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.Pullback.range_snd_of_isPullback p
  have hcomm (q : C.branchScheme k) :
      i ((a.branchSchemeIso (R := k)).hom q) =
        (a.singularLocusBlowupIso (R := k)).hom (i q) :=
    congrArg (fun v : C.branchScheme k ⟶ (C.singularLocus k).blowup ↦ v q)
      (a.branchSchemeIso_hom_branchSchemeToBlowup (R := k))
  rw [fixesNodalBranches_iff]
  constructor
  · intro h q
    apply i.injective
    have hq : i q ∈ (C.singularLocus k).blowupToBase ⁻¹'
        ((C.singularLocus k).support : Set C) := hRange ▸ Set.mem_range_self q
    exact (hcomm q).trans (h _ (Set.mem_preimage.mp hq))
  · intro h y hy
    obtain ⟨q, rfl⟩ : y ∈ Set.range i := hRange.symm ▸ hy
    simpa only [h q] using (hcomm q).symm

end

section Functoriality

variable {k : Type u} [Field k] {C D : Scheme.{u}}
  {f : C ⟶ Spec (.of k)} {g : D ⟶ Spec (.of k)}
  {hC : AtWorstNodalOfRelativeDimensionOne f} {hD : AtWorstNodalOfRelativeDimensionOne g}
  {a b : C ≅ C} {d : D ≅ D} {ha : a.hom ≫ f = f} {hb : b.hom ≫ f = f}
  {hd : d.hom ≫ g = g}

/-- The identity of a nodal curve fixes each branch. -/
@[simp]
theorem fixesNodalBranches_refl (hC : AtWorstNodalOfRelativeDimensionOne f) :
    (Iso.refl C).FixesNodalBranches f hC (by simp) := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have := hC.syntomic
  simp [fixesNodalBranches_iff_branchScheme]

/-- Composing two branch-fixing automorphisms fixes each branch. -/
theorem FixesNodalBranches.trans (h₁ : a.FixesNodalBranches f hC ha)
    (h₂ : b.FixesNodalBranches f hC hb) :
    (a ≪≫ b).FixesNodalBranches f hC (by rw [Iso.trans_hom, Category.assoc, hb, ha]) := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : a.hom.IsOver (Spec (.of k)) := ⟨ha⟩
  let : b.hom.IsOver (Spec (.of k)) := ⟨hb⟩
  have : SyntomicOfRelativeDimension 1 (C ↘ Spec (.of k)) := hC.syntomic
  rw [fixesNodalBranches_iff_branchScheme] at h₁ h₂ ⊢
  intro q
  rw [branchSchemeIso_trans (R := k) a b, Iso.trans_hom, Scheme.Hom.comp_apply, h₁, h₂]

/-- The inverse of a branch-fixing automorphism fixes each branch. -/
theorem FixesNodalBranches.symm (h : a.FixesNodalBranches f hC ha) :
    a.symm.FixesNodalBranches f hC (by rw [Iso.symm_hom, ← ha, Iso.inv_hom_id_assoc, ha]) := by
  have hinv : a.inv ≫ f = f := by rw [← ha, Iso.inv_hom_id_assoc, ha]
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : a.hom.IsOver (Spec (.of k)) := ⟨ha⟩
  let : a.symm.hom.IsOver (Spec (.of k)) := ⟨hinv⟩
  have : SyntomicOfRelativeDimension 1 (C ↘ Spec (.of k)) := hC.syntomic
  have hcomp := branchSchemeIso_trans (R := k) a a.symm
  simp only [a.self_symm_id, branchSchemeIso_refl] at hcomp
  rw [fixesNodalBranches_iff_branchScheme] at h ⊢
  intro q
  simpa only [Iso.refl_hom, Scheme.Hom.id_base, TopCat.coe_id, id_eq, Iso.trans_hom,
    Scheme.Hom.comp_apply, h q] using
    (congrArg (fun v : C.branchScheme k ≅ C.branchScheme k ↦ v.hom q) hcomp).symm

/-- An isomorphism of nodal curves intertwining two automorphisms transports branch
fixation in both directions. -/
theorem fixesNodalBranches_iff_of_comm (e : C ≅ D) (he : e.hom ≫ g = f)
    (hcomm : a ≪≫ e = e ≪≫ d) :
    a.FixesNodalBranches f hC ha ↔ d.FixesNodalBranches g hD hd := by
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : D.Over (Spec (.of k)) := ⟨g⟩
  let : e.hom.IsOver (Spec (.of k)) := ⟨he⟩
  let : a.hom.IsOver (Spec (.of k)) := ⟨ha⟩
  let : d.hom.IsOver (Spec (.of k)) := ⟨hd⟩
  have : SyntomicOfRelativeDimension 1 (C ↘ Spec (.of k)) := hC.syntomic
  have : SyntomicOfRelativeDimension 1 (D ↘ Spec (.of k)) := hD.syntomic
  have h : (a.branchSchemeIso (R := k)) ≪≫ (e.branchSchemeIso (R := k)) =
      (e.branchSchemeIso (R := k)) ≪≫ (d.branchSchemeIso (R := k)) := by
    rw [← branchSchemeIso_trans (R := k) a e, ← branchSchemeIso_trans (R := k) e d]
    congr 1
  rw [fixesNodalBranches_iff_branchScheme, fixesNodalBranches_iff_branchScheme]
  have hpoint (q : C.branchScheme k) :=
    congrArg (fun t : C.branchScheme k ≅ D.branchScheme k ↦ t.hom q) h
  simp only [Iso.trans_hom, Scheme.Hom.comp_apply] at hpoint
  refine ⟨fun ha q ↦ ?_, fun hd q ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := (e.branchSchemeIso (R := k)).hom.surjective q
    simpa only [ha p] using (hpoint p).symm
  · exact (e.branchSchemeIso (R := k)).hom.injective ((hpoint q).trans (hd _))

end Functoriality

variable {k : Type u} [Field k] {C : Scheme.{u}}
  [C.Over (Spec (.of k))] (hnodal : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k)))
  (g : C ≅ C) [g.hom.IsOver (Spec (.of k))]

local notation "S" => Scheme.singularLocus k C
local notation "N" => Scheme.IdealSheafData.blowup S
local notation "ν" => Scheme.IdealSheafData.blowupToBase S
local notation "gν" => Iso.hom (g.singularLocusBlowupIso (R := k))

private theorem disjoint_closures_preimage_of_disjoint_opens (U V : C.Opens)
    (hUV : Disjoint U V) :
    letI := hnodal.syntomic
    Disjoint (closure (ν ⁻¹' (U : Set C))) (closure (ν ⁻¹' (V : Set C))) := by
  have := hnodal.syntomic
  have : IsRegular N := C.isRegular_blowup_singularLocus hnodal
  have : IsFinite ν := C.isFinite_blowupToBase_singularLocus hnodal
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of k))
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian ν
  rw [Set.disjoint_left]
  intro z hzU hzV
  let A := irreducibleComponent z
  have hA : IsOpen A := isOpen_of_mem_irreducibleComponents_of_unique_minimalPrime_stalk
    (fun _ ↦ inferInstance) (irreducibleComponent_mem_irreducibleComponents z)
  have hzA : z ∈ A := mem_irreducibleComponent
  have hU : (A ∩ ν ⁻¹' (U : Set C)).Nonempty :=
    by simpa only [Set.inter_comm A] using
      (closure_inter_open_nonempty_iff hA).mp ⟨z, hzU, hzA⟩
  have hV : (A ∩ ν ⁻¹' (V : Set C)).Nonempty :=
    by simpa only [Set.inter_comm A] using
      (closure_inter_open_nonempty_iff hA).mp ⟨z, hzV, hzA⟩
  obtain ⟨w, _, hwU, hwV⟩ := (isIrreducible_irreducibleComponent (x := z)).isPreirreducible
    _ _ (U.isOpen.preimage (ν).continuous) (V.isOpen.preimage (ν).continuous) hU hV
  exact (Set.disjoint_left.mp (Opens.coe_disjoint.mpr hUV)) hwU hwV

private theorem exists_mem_closure_preimage_over (U : C.Opens) {x : C}
    (hx : x ∈ closure (U : Set C)) :
    letI := hnodal.syntomic
    ∃ z ∈ closure (ν ⁻¹' (U : Set C)), ν z = x := by
  have := hnodal.syntomic
  have : IsFinite ν := C.isFinite_blowupToBase_singularLocus hnodal
  have : Surjective ν := C.surjective_blowupToBase_singularLocus hnodal
  have heq := (ν).isClosedMap.closure_image_eq_of_continuous (ν).continuous
    (ν ⁻¹' (U : Set C))
  rwa [← Set.image_preimage_eq (U : Set C) (ν).surjective, heq] at hx

private theorem exists_distinct_over_of_mem_closure
    (U V : C.Opens) (hUV : Disjoint U V) {x : C}
    (hxU : x ∈ closure (U : Set C)) (hxV : x ∈ closure (V : Set C)) :
    letI := hnodal.syntomic
    ∃ a ∈ closure (ν ⁻¹' (U : Set C)), ∃ b ∈ closure (ν ⁻¹' (V : Set C)),
      ν a = x ∧ ν b = x ∧ a ≠ b := by
  have := hnodal.syntomic
  obtain ⟨a, ha, hax⟩ := exists_mem_closure_preimage_over hnodal U hxU
  obtain ⟨b, hb, hbx⟩ := exists_mem_closure_preimage_over hnodal V hxV
  have hd := Set.disjoint_left.mp (disjoint_closures_preimage_of_disjoint_opens hnodal U V hUV)
  exact ⟨a, ha, b, hb, hax, hbx, fun e ↦ hd ha (e.symm ▸ hb)⟩

/-- Two disjoint open subsets of a nodal curve can approach the same point only at a node. -/
theorem _root_.AlgebraicGeometry.Scheme.mem_support_singularLocus_of_mem_closures
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    (hnodal : AtWorstNodalOfRelativeDimensionOne (C ↘ Spec (.of k)))
    (U V : C.Opens) (hUV : Disjoint U V) {x : C}
    (hxU : x ∈ closure (U : Set C)) (hxV : x ∈ closure (V : Set C)) :
    letI := hnodal.syntomic
    x ∈ (C.singularLocus k).support := by
  have := hnodal.syntomic
  obtain ⟨a, _, b, _, hax, hbx, hab⟩ := exists_distinct_over_of_mem_closure hnodal U V hUV hxU hxV
  refine (C.mem_support_singularLocus_iff_notMem_smoothLocus x).mpr fun hx ↦ hab ?_
  exact C.eq_of_blowupToBase_singularLocus_eq_of_mem_smoothLocus
    (hax.trans hbx.symm) (hax.symm ▸ hx)

private theorem mapsTo_closure_preimage (U : C.Opens) (hU : Set.MapsTo g.hom U U) :
    letI := hnodal.syntomic
    Set.MapsTo gν (closure (ν ⁻¹' (U : Set C))) (closure (ν ⁻¹' (U : Set C))) := by
  have := hnodal.syntomic
  refine Set.MapsTo.closure ?_ (gν).continuous
  intro z hz
  have hw : ν (gν z) = g.hom (ν z) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f : N ⟶ C ↦ f z)
      (g.singularLocusBlowupIso_hom_blowupToBase (R := k))
  exact Set.mem_preimage.mpr (hw.symm ▸ hU hz)

/-- If a fixed point is approached by two disjoint invariant open subsets of a
nodal curve, it is a node and the automorphism fixes both normalization points. -/
theorem singularLocusBlowupIso_fixes_over_of_mem_closure [IsSepClosed k]
    (U V : C.Opens) (hUV : Disjoint U V)
    (hU : Set.MapsTo g.hom U U) (hV : Set.MapsTo g.hom V V) {x : C}
    (hxU : x ∈ closure (U : Set C)) (hxV : x ∈ closure (V : Set C)) (hx : g.hom x = x) :
    letI := hnodal.syntomic
    x ∈ (S).support ∧ ∀ {z : N}, ν z = x → gν z = z := by
  have := hnodal.syntomic
  obtain ⟨a, ha, b, hb, hax, hbx, hab⟩ := exists_distinct_over_of_mem_closure hnodal U V hUV hxU hxV
  have hd := Set.disjoint_left.mp (disjoint_closures_preimage_of_disjoint_opens hnodal U V hUV)
  have hsing := C.mem_support_singularLocus_of_mem_closures hnodal U V hUV hxU hxV
  refine ⟨hsing, ?_⟩
  let F := ν ⁻¹' ({x} : Set C)
  have hcard : F.ncard = 2 :=
    C.natCard_preimage_blowupToBase_singularLocus_eq_two_of_mem_support hnodal hsing
  have hF : F = {a, b} :=
    (Set.eq_of_subset_of_ncard_le (Set.insert_subset_iff.mpr
      ⟨hax, Set.singleton_subset_iff.mpr hbx⟩) (by rw [hcard, Set.ncard_pair hab])
      (Set.finite_of_ncard_ne_zero (hcard.trans_ne (by decide)))).symm
  have hmap : Set.MapsTo gν F F := by
    intro z hz
    have hw : ν (gν z) = g.hom (ν z) := by
      simpa only [Scheme.Hom.comp_apply] using congrArg (fun f : N ⟶ C ↦ f z)
        (g.singularLocusBlowupIso_hom_blowupToBase (R := k))
    exact hw.trans ((congrArg g.hom hz).trans hx)
  have hfa : gν a = a := by
    simpa only [hF, Set.mem_insert_iff, Set.mem_singleton_iff, or_iff_left
      (fun h : gν a = b ↦ hd (mapsTo_closure_preimage hnodal g U hU ha) (h.symm ▸ hb))]
      using hmap hax
  have hfb : gν b = b := by
    simpa only [hF, Set.mem_insert_iff, Set.mem_singleton_iff, or_iff_right
      (fun h : gν b = a ↦ hd (h.symm ▸ ha) (mapsTo_closure_preimage hnodal g V hV hb))]
      using hmap hbx
  intro z hz
  have hzF : z ∈ ({a, b} : Set N) := hF ▸ (hz : z ∈ F)
  rcases Set.mem_insert_iff.mp hzF with rfl | hz'
  · exact hfa
  · rcases Set.mem_singleton_iff.mp hz' with rfl
    exact hfb

end CategoryTheory.Iso
