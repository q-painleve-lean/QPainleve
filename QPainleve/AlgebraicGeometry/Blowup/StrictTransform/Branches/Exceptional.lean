/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Attachments
public import QPainleve.AlgebraicGeometry.Curves.Node.NormalizationComponent

import QPainleve.AlgebraicGeometry.Blowup.Descent
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.FirstKind
import QPainleve.AlgebraicGeometry.Blowup.Smooth
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Cartier
import QPainleve.AlgebraicGeometry.Curves.Node.BoundaryRestriction
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Integral
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.VanishingIdeal
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# The exceptional component of a normalized boundary

The exceptional divisor of a point blowup appears unchanged as a component of
the normalization of the reduced total boundary. At each attachment above a
blown-up node, exactly one branch belongs to this component. These are the
exceptional branches in the subdivision of a boundary cycle under a toric blowup
of a Looijenga pair, as in [Gross, Hacking and Keel, §1][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
  {p : D.subscheme} (hc : IsClosed ({D.subschemeι p} : Set X))

local notation "base" => (X ↘ Spec (CommRingCat.of k))
local notation "I" =>
  vanishingIdeal (Closeds.mk (closure ({D.subschemeι p} : Set X)) isClosed_closure)
local notation "π" => blowupToBase (I)
local notation "E" => IdealSheafData.comap (I) (π)
local notation "R" => radical (IdealSheafData.comap D (π))
local notation "B" => subscheme (R)
local notation "j" => subschemeι (R)
local notation "N" => blowup (Scheme.singularLocus k (B))
local notation "ν" => blowupToBase (Scheme.singularLocus k (B))

omit [IsIntegral X] in
include hc in
private theorem exceptional_support_le :
    (E).support ≤ (R).support := by
  have hpD : D.subschemeι p ∈ D.support :=
    D.range_subschemeι.le (Set.mem_range_self _)
  have hDI : D ≤ (I) := (X.ker_fromSpecResidueField_eq_vanishingIdeal (D.subschemeι p)) ▸
    (D.le_ker_fromSpecResidueField_iff_mem_support hc).mpr hpD
  rw [support_radical]
  exact support_antitone (comap_mono (π) hDI)

variable [(D.comap (vanishingIdeal
  ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme.Over
    (Spec (.of k))]
  [PrestableFamily ((D.comap (vanishingIdeal
    ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
      Spec (.of k))]

include hD hc in
private theorem exists_exceptionalNormalizationComponent [IsReduced D.subscheme] :
    ∃ v : irreducibleComponents (N),
      Set.range (((B).blowupComponent (K := k) v).ι ≫ (ν) ≫ (j)) =
        Set.range (E).subschemeι := by
  have : Smooth base := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian base
  have : IsLocallyNoetherian (I).blowup := LocallyOfFiniteType.isLocallyNoetherian (π)
  have := isRegularLocalRing_stalk_of_smooth base (D.subschemeι p)
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq base 2).mp
    inferInstance).2 _ hc
  have : IsIntegral (E).subscheme := isIntegral_exceptional_blowup_closed_point hdim hc
  let q : CodimensionOnePoint (I).blowup := ⟨(E).subschemeι (genericPoint (E).subscheme),
    (I).isEffectiveCartier_comap_blowupToBase.coheight_subschemeι_genericPoint⟩
  have hq : (q : (I).blowup) ∈ (E).support :=
    (E).range_subschemeι.le (Set.mem_range_self _)
  have hR : (R).IsEffectiveCartier :=
    hD.radical_comap_blowupToBase_of_closedPoint base hc
      (D.range_subschemeι.le (Set.mem_range_self p))
  obtain ⟨v, hv⟩ := hR.exists_range_blowupComponent_comp_subschemeι
    (k := k) (p := q) ((exceptional_support_le hc) hq)
  refine ⟨v, hv.trans ?_⟩
  simpa only [q, Set.image_singleton, genericPoint_closure, Set.image_univ] using
    ((E).subschemeι.isClosedMap.closure_image_eq_of_continuous (E).subschemeι.continuous
      {genericPoint (E).subscheme})

variable [IsReduced D.subscheme]

/-- The component of the normalized reduced boundary lying over the exceptional divisor. -/
def exceptionalNormalizationComponent : irreducibleComponents (N) :=
  (exists_exceptionalNormalizationComponent (k := k) hD hc).choose

local notation "U" =>
  Scheme.blowupComponent (K := k) (B) (exceptionalNormalizationComponent (k := k) hD hc)

/-- The exceptional normalization component maps onto the exceptional divisor in the blowup. -/
theorem range_exceptionalNormalizationComponent :
    Set.range ((U).ι ≫ (ν) ≫ (j)) = Set.range (E).subschemeι :=
  (exists_exceptionalNormalizationComponent (k := k) hD hc).choose_spec

include hD hc in
private theorem exists_exceptionalNormalizationIso :
    ∃ e : (U).toScheme ≅ (E).subscheme,
      e.hom ≫ (E).subschemeι = (U).ι ≫ (ν) ≫ (j) := by
  have : Smooth base := SmoothOfRelativeDimension.smooth 2 _
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian base
  have := isRegularLocalRing_stalk_of_smooth base (D.subschemeι p)
  have hdim := ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq base 2).mp
    inferInstance).2 _ hc
  have : IsIntegral (E).subscheme := isIntegral_exceptional_blowup_closed_point hdim hc
  obtain ⟨e, _, _⟩ :=
    exists_iso_projectiveLine_pullback_exceptionalIdeal_of_closedPoint (D.subschemeι p) hc hdim
  have : IsRegular (projectiveLine (X.residueField (D.subschemeι p))) :=
    ⟨fun _ ↦ inferInstance⟩
  have hreg := IsRegular.of_isOpenImmersion e.inv
  rw [X.ker_fromSpecResidueField_eq_vanishingIdeal] at hreg
  have : IsRegular (E).subscheme := hreg
  let l := IsClosedImmersion.lift (j) (E).subschemeι (by
    rw [ker_subschemeι, ← vanishingIdeal_support]
    exact vanishingIdeal_le_ker_of_range_subset _ (by
      rw [range_subschemeι]
      exact exceptional_support_le hc))
  have hl : l ≫ (j) = (E).subschemeι := IsClosedImmersion.lift_fac _ _ _
  have : IsClosedImmersion (l ≫ (j)) := hl.symm ▸ inferInstanceAs
    (IsClosedImmersion (E).subschemeι)
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l (j)
  have hrange : Set.range ((U).ι ≫ (ν)) = Set.range l := by
    apply (j).injective.image_injective
    rw [← Set.range_comp, ← Set.range_comp]
    -- The underlying functions of composites agree with the scheme composites.
    change Set.range (⇑(((U).ι ≫ (ν)) ≫ (j))) = Set.range (⇑(l ≫ (j)))
    rw [Category.assoc, hl]
    exact range_exceptionalNormalizationComponent hD hc
  obtain ⟨e', he'⟩ := ((B).existsUnique_blowupComponentIso_of_range_eq l _ hrange).exists
  refine ⟨e', ?_⟩
  rw [← hl, ← Category.assoc, he', Category.assoc]

/-- The exceptional component of the normalization is isomorphic to the actual
exceptional divisor of the surface blowup. -/
def exceptionalNormalizationIso : (U).toScheme ≅ (E).subscheme :=
  (exists_exceptionalNormalizationIso hD hc).choose

/-- The exceptional component isomorphism commutes with the two maps to the surface blowup. -/
@[reassoc (attr := simp)]
theorem exceptionalNormalizationIso_hom_subschemeι :
    (exceptionalNormalizationIso hD hc).hom ≫ (E).subschemeι = (U).ι ≫ (ν) ≫ (j) :=
  (exists_exceptionalNormalizationIso hD hc).choose_spec

/-- The normalized exceptional component projects bijectively onto the exceptional
locus in the reduced total boundary. At a node of that locus this selects one branch. -/
theorem bijOn_blowupToBase_exceptionalNormalizationComponent :
    Set.BijOn (ν) ((U) : Set (N)) ((j) ⁻¹' ((E).support : Set (I).blowup)) := by
  let e := exceptionalNormalizationIso (k := k) hD hc
  have he (y : (U).toScheme) :
      (E).subschemeι (e.hom y) = (j) ((ν) y.val) := by
    have hy : (U).ι y = y.val := (rfl)
    simpa only [e, Scheme.Hom.comp_apply, hy] using
      congrArg (fun g : (U).toScheme ⟶ (I).blowup ↦ g y)
        (exceptionalNormalizationIso_hom_subschemeι hD hc)
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rw [Set.mem_preimage, ← he ⟨y, hy⟩, ← (E).range_subschemeι]
    exact Set.mem_range_self _
  · intro x hx y hy hxy
    have h : e.hom ⟨x, hx⟩ = e.hom ⟨y, hy⟩ :=
      (E).subschemeι.injective ((he ⟨x, hx⟩).trans (hxy ▸ (he ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (e.hom.injective h)
  · intro z hz
    have hz' : (j) z ∈ Set.range (E).subschemeι := (E).range_subschemeι.ge hz
    rw [← range_exceptionalNormalizationComponent (k := k) hD hc] at hz'
    obtain ⟨y, hy⟩ := hz'
    refine ⟨y.val, y.property, (j).injective ?_⟩
    have hy' : (U).ι y = y.val := (rfl)
    simpa only [Scheme.Hom.comp_apply, hy'] using hy

/-- A point on the exceptional locus of the reduced boundary has a unique
normalization point on the exceptional component. -/
theorem existsUnique_blowupToBase_eq_of_mem_exceptional {z : (B)}
    (hz : (j) z ∈ (E).support) :
    ∃! y : (N), (ν) y = z ∧ y ∈ (U) := by
  have h := bijOn_blowupToBase_exceptionalNormalizationComponent (k := k) hD hc
  obtain ⟨y, hy, hyz⟩ := h.surjOn hz
  exact ⟨y, ⟨hyz, hy⟩, fun x hx ↦ h.injOn hx.2 hy (hx.1.trans hyz.symm)⟩

/-- Each attachment node has one normalization point on the exceptional
component and one on a strict component, even when the blown-up node is a self-node. -/
theorem existsUnique_blowupToBase_eq_and_notMem_exceptionalNormalizationComponent [IsSepClosed k]
    {z : (B)} (hz : (j) z ∈ (E).support) (hnode : z ∈ (Scheme.singularLocus k (B)).support) :
    ∃! y : (N), (ν) y = z ∧ y ∉ (U) := by
  obtain ⟨x, hx, huniq⟩ :=
    existsUnique_blowupToBase_eq_of_mem_exceptional (k := k) hD hc hz
  let a : (ν) ⁻¹' ({z} : Set (B)) := ⟨x, hx.1⟩
  have hc₂ := (B).natCard_preimage_blowupToBase_singularLocus_eq_two_of_mem_support
    PrestableFamily.atWorstNodalOfRelativeDimensionOne hnode
  obtain ⟨b, hb, hbuniq⟩ := (Nat.card_eq_two_iff' a).mp hc₂
  refine ⟨b.val, ⟨b.property, fun hm ↦ hb (Subtype.ext (huniq _ ⟨b.property, hm⟩))⟩, ?_⟩
  intro y hy
  let y' : (ν) ⁻¹' ({z} : Set (B)) := ⟨y, hy.1⟩
  have hne : y' ≠ a := by
    intro e
    have hv : y = x := congrArg Subtype.val e
    exact hy.2 (hv.symm ▸ hx.2)
  exact congrArg Subtype.val (hbuniq y' hne)

section AttachmentBranches

local notation "C" => IdealSheafData.subscheme D
local notation "S[" W "]" => Scheme.singularLocus k W
local notation "nodal[" W "]" =>
  PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := W ↘ Spec (CommRingCat.of k))
local notation "f" => subschemeMap (R) D (π)
  (le_map_iff_comap_le.mpr (le_radical _))

private theorem bijOn_blowupToBase_exceptionalAttachmentBranches :
    Set.BijOn (ν) {y : (N) | y ∈ (U) ∧ (ν) y ∈ (S[(B)]).support}
      {z : (B) | z ∈ (S[(B)]).support ∧ (f) z = p} := by
  have h := bijOn_blowupToBase_exceptionalNormalizationComponent (k := k) hD hc
  refine ⟨fun y hy ↦ ⟨hy.2, (mem_exceptional_iff_boundaryMap_eq hc _).mp (h.mapsTo hy.1)⟩,
    ?_, ?_⟩
  · exact h.injOn.mono fun _ hy ↦ hy.1
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := h.surjOn ((mem_exceptional_iff_boundaryMap_eq hc z).mpr hz.2)
    exact ⟨y, ⟨hy, hyz.symm ▸ hz.1⟩, hyz⟩

variable [D.subscheme.Over (Spec (.of k))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k))] [PerfectField k]

variable (hCOver : D.subscheme ↘ Spec (.of k) = D.subschemeι ≫ X ↘ Spec (.of k))
  (hBOver : (D.comap (vanishingIdeal
    ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subscheme ↘
      Spec (.of k) =
    (D.comap (vanishingIdeal
      ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase).radical.subschemeι ≫
          (vanishingIdeal ⟨closure ({D.subschemeι p} : Set X), isClosed_closure⟩).blowupToBase ≫
            X ↘ Spec (.of k))
  (hp : p ∈ (D.subscheme.singularLocus k).support)

local notation "attach" => branchEquivSingularFiber hD nodal[(C)] hc hCOver hBOver hp nodal[(B)]

/-- An original branch at the center labels the exceptional-side branch of its
attachment node. These are all the branches on the normalized exceptional component. -/
def exceptionalNormalizationBranchEquiv :
    {b : (C).branchScheme k | (S[(C)]).subschemeι ((C).branchSchemeToSingularLocus k b) = p} ≃
      {y : (N) | y ∈ (U) ∧ (ν) y ∈ (S[(B)]).support} :=
  (attach).trans ((bijOn_blowupToBase_exceptionalAttachmentBranches hD hc).equiv _).symm

/-- The exceptional-side point labelled by an old branch projects to its attachment node. -/
@[simp]
theorem blowupToBase_exceptionalNormalizationBranchEquiv
    (b : {b : (C).branchScheme k |
      (S[(C)]).subschemeι ((C).branchSchemeToSingularLocus k b) = p}) :
    (ν) (exceptionalNormalizationBranchEquiv hD hc hCOver hBOver hp b).val =
      ((attach) b).val :=
  congrArg Subtype.val
    (((bijOn_blowupToBase_exceptionalAttachmentBranches hD hc).equiv _).apply_symm_apply
      ((attach) b))

end AttachmentBranches

section NormalizationLift

variable [D.subscheme.Over (Spec (.of k))]
  [PrestableFamily (D.subscheme ↘ Spec (.of k))]

local notation "ν₀" => blowupToBase (Scheme.singularLocus k D.subscheme)

/-- Any lift of the reduced boundary projection to the normalizations sends the
entire exceptional component to one point over the blown-up node. In particular
it sends the exceptional branches of both attachments to the same old branch. -/
theorem eq_of_mem_exceptionalNormalizationComponent_of_comp_eq
    {g : (N) ⟶ blowup (Scheme.singularLocus k D.subscheme)}
    (hg : g ≫ (ν₀) ≫ D.subschemeι = (ν) ≫ (j) ≫ (π))
    {x y : (N)} (hx : x ∈ (U)) (hy : y ∈ (U)) :
    g x = g y := by
  let v := exceptionalNormalizationComponent (k := k) hD hc
  have hmap : Set.MapsTo g (v : Set (N)) ((ν₀) ⁻¹' {p}) := by
    intro a ha
    have haU : a ∈ (U) := by rwa [← (B).coe_blowupComponent v] at ha
    have he := (bijOn_blowupToBase_exceptionalNormalizationComponent hD hc).mapsTo haU
    have heq : (j) ((ν) a) ∈ (π) ⁻¹' {D.subschemeι p} :=
      range_subschemeι_comap_pointBlowup hc ▸ (E).range_subschemeι.ge he
    have h := congrArg (fun t : (N) ⟶ X ↦ t a) hg
    simp only [Scheme.Hom.comp_apply] at h
    exact D.subschemeι.injective (h.trans heq)
  have : IsFinite (ν₀) := D.subscheme.isFinite_blowupToBase_singularLocus
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hd := (ν₀).isDiscrete_preimage_singleton p
  have hd' := hd.mono (Set.mapsTo_iff_image_subset.mp hmap)
  have hirr := v.property.1.isPreirreducible.image g g.continuous.continuousOn
  have hmem (a : (N)) : a ∈ (U) ↔ a ∈ (v : Set (N)) :=
    Set.ext_iff.mp ((B).coe_blowupComponent (K := k) v) a
  exact (hd'.subsingleton_of_isPreirreducible hirr)
    ⟨x, (hmem x).mp hx, rfl⟩ ⟨y, (hmem y).mp hy, rfl⟩

end NormalizationLift

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
