/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Map
public import QPainleve.AlgebraicGeometry.Curves.Node.NormalizationComponent

import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Rescaling
import QPainleve.AlgebraicGeometry.Curves.Node.PointBlowup
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Normalization.Lift

/-!
# Lifting maps to the normalizations of nodal curves

On each normalization component mapping generically into the smooth locus,
the lift is forced by the isomorphism over that locus. On a component mapped
to a node, either branch over the node may be chosen as the constant value.
These choices supply the lift for comparing periods under subdivision of a
nodal boundary. On each oriented cycle the period is the gluing product of
[Gross, Hacking and Keel, Lemma 2.1](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "N[" C "]" => blowup (Scheme.singularLocus k C)
local notation "ν[" C "]" => blowupToBase (Scheme.singularLocus k C)
local notation "smooth[" C "]" => Scheme.Hom.smoothLocus (C ↘ S)
local notation "nodal[" C "]" =>
  PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := C ↘ S)

private theorem existsUnique_lift_from_smoothLocus {C : Scheme.{u}} [IsIntegral C]
    [IsNormalScheme C] (f : C ⟶ Y) (hf : f (genericPoint C) ∈ smooth[Y]) :
    ∃! g : C ⟶ N[Y], g ≫ ν[Y] = f := by
  let a := C.fromSpecStalk (genericPoint C)
  have hU : Set.range (a ≫ f) ⊆ Set.range (smooth[Y]).ι := by
    rw [Scheme.Opens.range_ι]
    have hη : (a ≫ f) (IsLocalRing.closedPoint (C.presheaf.stalk (genericPoint C))) ∈
        smooth[Y] := by
      have he : (a ≫ f) (IsLocalRing.closedPoint (C.presheaf.stalk (genericPoint C))) =
          f (genericPoint C) := congrArg (fun z : C ↦ f z) Scheme.fromSpecStalk_closedPoint
      exact he.symm ▸ hf
    have htop := Scheme.preimage_eq_top_of_closedPoint_mem (a ≫ f) hη
    rintro _ ⟨z, rfl⟩
    exact (a ≫ f).mem_preimage.mp (by rw [htop]; exact Opens.mem_top z)
  let t := IsOpenImmersion.lift (smooth[Y]).ι (a ≫ f) hU
  have : IsIso (ν[Y] ∣_ smooth[Y]) :=
    Y.isIso_blowupToBase_singularLocus_restrict_smoothLocus
  have : IsFinite ν[Y] := Y.isFinite_blowupToBase_singularLocus nodal[Y]
  let P := isPullback_morphismRestrict ν[Y] smooth[Y]
  let s := t ≫ inv (ν[Y] ∣_ smooth[Y]) ≫ (ν[Y] ⁻¹ᵁ smooth[Y]).ι
  have hs : s ≫ ν[Y] = a ≫ f := by simp [s, t, ← morphismRestrict_ι]
  obtain ⟨g, ⟨hg, -⟩, huniq⟩ := f.existsUnique_lift_of_isIntegralHom ν[Y] s hs
  refine ⟨g, hg, fun g' hg' ↦ huniq g' ⟨hg', ?_⟩⟩
  have hcomm : t ≫ (smooth[Y]).ι = (a ≫ g') ≫ ν[Y] := by simp [t, hg']
  let l := P.lift t (a ≫ g') hcomm
  have hl : l = t ≫ inv (ν[Y] ∣_ smooth[Y]) := by
    apply (cancel_mono (ν[Y] ∣_ smooth[Y])).mp
    simp only [l, IsPullback.lift_fst, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  calc
    a ≫ g' = l ≫ (ν[Y] ⁻¹ᵁ smooth[Y]).ι := (P.lift_snd _ _ _).symm
    _ = s := by simp only [hl, s, Category.assoc]

section BranchChoice

variable [IsAlgClosed k] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]

local notation "j" => Scheme.branchSchemeToBlowup k Y
local notation "V" => irreducibleComponents N[X]
local notation "comp[" v "]" => Scheme.Opens.toScheme (X.blowupComponent (K := k) v)
local notation "ι[" v "]" => Scheme.Opens.ι (X.blowupComponent (K := k) v)
local notation "F[" v "]" => ι[v] ≫ ν[X] ≫ f
local notation "imageGeneric[" v "]" => (F[v]) (genericPoint comp[v])

private theorem existsUnique_lift_of_branch (v : V) (b : Y.branchScheme k)
    (hb : ν[Y] (j b) = imageGeneric[v]) :
    ∃! g : comp[v] ⟶ N[Y], g ≫ ν[Y] = F[v] ∧ ∀ x : comp[v], g x = j b := by
  let r := Y.branchRationalPoint nodal[Y] b ≫ j
  let q := ν[Y] ≫ Y ↘ S
  have hr : r ≫ q = 𝟙 _ := by
    simp only [r, q, Category.assoc, ← branchSchemeToSingularLocus_subschemeι_assoc,
      comp_over, branchRationalPoint_comp]
  have hrp (x : S) : r x = j b := by simp [r]
  have hj : j b ∈ ν[Y] ⁻¹' ((Y.singularLocus k).support : Set Y) :=
    Y.range_branchSchemeToBlowup.le ⟨b, rfl⟩
  have hp : imageGeneric[v] ∈ (Y.singularLocus k).support := by
    simpa only [Set.mem_preimage, SetLike.mem_coe, hb] using hj
  have hc := Y.isClosed_singleton_of_mem_singularLocus nodal[Y] hp
  have hconst (x : comp[v]) : F[v] x = imageGeneric[v] := by
    have hx := (genericPoint_specializes x).map (F[v]).continuous
    exact Set.mem_singleton_iff.mp (hx.mem_closed hc (Set.mem_singleton _))
  let g := (comp[v] ↘ S) ≫ r
  have hsection : (r ≫ ν[Y]) ≫ (Y ↘ S) = 𝟙 _ := by
    simpa only [Category.assoc, q] using hr
  have : IsClosedImmersion (r ≫ ν[Y]) :=
    isClosedImmersion_of_comp_eq_id _ _ hsection
  have hFg : F[v] = F[v] ≫ (Y ↘ S) ≫ (r ≫ ν[Y]) := by
    apply (F[v]).eq_comp_of_range_subset_of_section (Y ↘ S) (r ≫ ν[Y]) hsection
    rintro _ ⟨x, rfl⟩
    exact ⟨(comp[v] ↘ S) x,
      (congrArg (ν[Y]) (hrp _)).trans (hb.trans (hconst x).symm)⟩
  have hFover : F[v] ≫ (Y ↘ S) = comp[v] ↘ S := by
    simp only [Category.assoc, comp_over, Scheme.blowupComponent_over]
  have hg : g ≫ ν[Y] = F[v] := by
    calc
      g ≫ ν[Y] = ((F[v]) ≫ (Y ↘ S)) ≫ (r ≫ ν[Y]) := by
        rw [hFover]
        simp only [g, Category.assoc]
      _ = F[v] := hFg.symm
  refine ⟨g, ⟨hg, fun x ↦ hrp ((comp[v] ↘ S) x)⟩, fun g' ⟨hg', hv'⟩ ↦ ?_⟩
  have : IsClosedImmersion r := isClosedImmersion_of_comp_eq_id _ _ hr
  have hrep := g'.eq_comp_of_range_subset_of_section q r hr (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(comp[v] ↘ S) x, (hrp _).trans (hv' x).symm⟩)
  have hbase : g' ≫ q = comp[v] ↘ S := by
    calc
      g' ≫ q = (g' ≫ ν[Y]) ≫ (Y ↘ S) := (Category.assoc _ _ _).symm
      _ = comp[v] ↘ S := (congrArg (· ≫ (Y ↘ S)) hg').trans hFover
  exact hrep.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ r) hbase))

/-- A morphism of prestable curves lifts to their normalizations once one target branch
has been chosen for each normalized source component sent to a node. The lift is
unique with these choices and is constant at the chosen branch on each such component.
Different components contracted to the same node can choose independently, including
when the node is a self-node. -/
theorem existsUnique_nodal_normalization_lift
    (b : ∀ v : V, imageGeneric[v] ∈ (Y.singularLocus k).support → Y.branchScheme k)
    (hb : ∀ v h, ν[Y] (j (b v h)) = imageGeneric[v]) :
    ∃! g : N[X] ⟶ N[Y], g ≫ ν[Y] = ν[X] ≫ f ∧
      ∀ v h (x : comp[v]), g (ι[v] x) = j (b v h) := by
  classical
  let 𝒰 := (N[X]).openCoverOfIsOpenCover (X.blowupComponent (K := k))
    (X.iSup_blowupComponent (k := k))
  have hlocal (v : V) : ∃! g : comp[v] ⟶ N[Y],
      g ≫ ν[Y] = ι[v] ≫ ν[X] ≫ f ∧ ∀ h (x : comp[v]), g x = j (b v h) := by
    by_cases h : imageGeneric[v] ∈ (Y.singularLocus k).support
    · obtain ⟨g, hg, huniq⟩ := existsUnique_lift_of_branch f v (b v h) (hb v h)
      exact ⟨g, ⟨hg.1, fun _ ↦ hg.2⟩, fun g' hg' ↦ huniq g' ⟨hg'.1, hg'.2 h⟩⟩
    · have : IsRegular N[X] := X.isRegular_blowup_singularLocus nodal[X]
      have : IsRegular comp[v] := IsRegular.of_isOpenImmersion (ι[v])
      have : IsNormalScheme comp[v] := inferInstance
      have hs : imageGeneric[v] ∈ smooth[Y] := by
        simpa only [Y.mem_support_singularLocus_iff_notMem_smoothLocus, not_not] using h
      obtain ⟨g, hg, huniq⟩ := existsUnique_lift_from_smoothLocus (ι[v] ≫ ν[X] ≫ f) hs
      exact ⟨g, ⟨hg, fun h' ↦ (h h').elim⟩, fun g' hg' ↦ huniq g' hg'.1⟩
  let g (v : V) := (hlocal v).exists.choose
  have hg (v : V) := (hlocal v).exists.choose_spec
  have hglue (v w : V) :
      pullback.fst (ι[v]) (ι[w]) ≫ g v = pullback.snd _ _ ≫ g w := by
    by_cases h : v = w
    · subst w
      rw [(cancel_mono (ι[v])).mp pullback.condition]
    · have hempty : IsEmpty ↥(pullback (ι[v]) (ι[w])) := by
        apply Scheme.isEmpty_pullback
        simpa only [Scheme.Opens.range_ι, ← TopologicalSpace.Opens.coe_disjoint]
          using X.pairwise_disjoint_blowupComponent h
      exact (isInitialOfIsEmpty (X := pullback (ι[v]) (ι[w]))).hom_ext _ _
  let lift := 𝒰.glueMorphisms g hglue
  have hl (v : V) : ι[v] ≫ lift = g v := 𝒰.ι_glueMorphisms g hglue v
  refine ⟨lift, ⟨?_, ?_⟩, ?_⟩
  · refine 𝒰.hom_ext _ _ (fun (v : V) ↦ ?_)
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ ν[Y]) (hl v))).trans (hg v).1
  · intro v h x
    rw [← Hom.comp_apply, hl v]
    exact (hg v).2 h x
  · rintro g' ⟨hg', hb'⟩
    refine 𝒰.hom_ext _ _ (fun (v : V) ↦ ?_)
    have heq : ι[v] ≫ g' = g v :=
      (hlocal v).unique ⟨by rw [Category.assoc, hg'], hb' v⟩ (hg v)
    exact heq.trans (hl v).symm

/-- Every morphism of prestable curves over an algebraically closed field admits a lift
to the blowups of the singular loci. Each component contracted to a node can use either
of the branches over that node. -/
theorem exists_nodal_normalization_lift :
    ∃ g : N[X] ⟶ N[Y], CommSq ν[X] g f ν[Y] := by
  have : Surjective ν[Y] := Y.surjective_blowupToBase_singularLocus nodal[Y]
  have hbranch (v : V) (h : imageGeneric[v] ∈ (Y.singularLocus k).support) :
      ∃ b : Y.branchScheme k, ν[Y] (j b) = imageGeneric[v] := by
    obtain ⟨y, hy⟩ := (ν[Y]).surjective imageGeneric[v]
    have hy' : y ∈ ν[Y] ⁻¹' ((Y.singularLocus k).support : Set Y) := by
      simpa only [Set.mem_preimage, SetLike.mem_coe, hy] using h
    obtain ⟨b, rfl⟩ := Y.range_branchSchemeToBlowup.ge hy'
    exact ⟨b, hy⟩
  choose b hb using hbranch
  obtain ⟨g, ⟨hg, -⟩, -⟩ := f.existsUnique_nodal_normalization_lift b hb
  exact ⟨g, ⟨hg.symm⟩⟩

end BranchChoice

end AlgebraicGeometry.Scheme.Hom
