/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Contraction
public import QPainleve.AlgebraicGeometry.Curves.Node.Locus

import QPainleve.AlgebraicGeometry.Blowup.Integral
import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Node
import QPainleve.AlgebraicGeometry.Curves.Node.Order
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Subtraction
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Nodality under anticanonical point blowdown

A nodal anticanonical boundary descends to a nodal boundary under a closed-point
blowdown. When the boundary contains the exceptional curve, the two attachments
of the residual boundary produce a node, including a self-node.

This is the boundary contraction in [Gross, Hacking and Keel, *Mirror symmetry
for log Calabi–Yau surfaces I*, Proposition 1.3]
(https://arxiv.org/html/1106.4977v3#S1.Thmproposition3).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "I" => vanishingIdeal (Closeds.mk (closure (Singleton.singleton p)) isClosed_closure)
local notation "π" => blowupToBase I
local notation "E" => comap I π
local notation "strict(" D ")" => Scheme.Hom.ker (blowupMap I (subschemeι D))
local notation "S" => Spec (CommRingCat.of k)
local notation "s" => (X ↘ S)
local notation "K(" W ")" => LineBundleClass.mk (QPainleve.canonicalBundle k W 2)

omit [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] in
private theorem atWorstNodalOfRelativeDimensionOne_of_pointBlowdown
    {D : X.IdealSheafData} {B : (I).blowup.IdealSheafData}
    (hD : D.comap π = B * E)
    (hB : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ π ≫ s))
    (hp : IsClosed ({p} : Set X))
    (hnode : ∀ q : D.subscheme, D.subschemeι q = p → (D.subschemeι ≫ s).IsNodeAt q) :
    AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s) := by
  classical
  let V : X.Opens := (I).support.compl
  let U : (I).blowup.Opens := π ⁻¹ᵁ V
  have hπ : U.ι ≫ π = (π ∣_ V) ≫ V.ι := (morphismRestrict_ι π V).symm
  have : IsOpenImmersion (U.ι ≫ π) := hπ ▸ inferInstanceAs (IsOpenImmersion ((π ∣_ V) ≫ V.ι))
  have hU : (E).support.compl = U := compl_support_comap _ _
  have hE : (E).comap U.ι = ⊤ :=
    (comap_eq_top_iff _ _).mpr (hU.symm ▸ Scheme.Opens.ι_preimage_self U)
  have hDE : D.comap (U.ι ≫ π) = B.comap U.ι := by
    rw [comap_comp, hD, comap_mul, hE, mul_top]
  have hRange : Set.range (U.ι ≫ π) = ({p} : Set X)ᶜ := by
    rw [hπ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso _).surjective,
      Set.image_univ, Scheme.Opens.range_ι, Closeds.coe_compl, coe_support_vanishingIdeal,
      Closeds.coe_mk, hp.closure_eq]
  have hlocal (q : D.subscheme) :
      ∃ (W : Scheme.{u}) (j : W ⟶ D.subscheme), IsOpenImmersion j ∧ q ∈ Set.range j ∧
        AtWorstNodalOfRelativeDimensionOne (j ≫ D.subschemeι ≫ s) := by
    by_cases hq : D.subschemeι q = p
    · exact (hnode q hq).exists_nodal_neighbourhood
    · exact D.exists_nodal_neighbourhood_of_comap_eq (U.ι ≫ π) U.ι
        (by simp only [Category.assoc]) hDE hB q (by
          rw [hRange, Set.mem_compl_iff, Set.mem_singleton_iff]
          exact hq)
  choose W j hj hmem hnodal using hlocal
  let (q : D.subscheme) : IsOpenImmersion (j q) := hj q
  let cover : D.subscheme.OpenCover := Scheme.Cover.mkOfCovers D.subscheme W j (fun q ↦ ⟨q, hmem q⟩)
  exact IsZariskiLocalAtSource.of_openCover (P := @AtWorstNodalOfRelativeDimensionOne)
    cover hnodal

variable (k) [IsAlgClosed k] [NeZero (2 : k)] [X.IsProjectiveOver k] [IsIntegral X]

/-- A nodal anticanonical boundary on a point blowup descends to its nodal
anticanonical schematic image. The total transform adds the exceptional curve once.
The center is a node precisely when the original boundary contains that curve. -/
theorem IsEffectiveCartier.anticanonical_nodal_boundary_point_blowdown
    (hp : IsClosed ({p} : Set X)) {B : (I).blowup.IdealSheafData} (hB : B.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (B.subschemeι ≫ π ≫ s)) :
    let : (I).blowup.Over S := ⟨π ≫ s⟩
    let : SmoothOfRelativeDimension 2 ((I).blowup ↘ S) :=
      smoothOfRelativeDimension_blowup_closed_point s hp
    LineBundleClass.mk hB.toInvertibleSheaf = K((I).blowup) →
    let D := B.map π
    ∃ hD : D.IsEffectiveCartier, LineBundleClass.mk hD.toInvertibleSheaf = K(X) ∧
      AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ s) ∧ D.comap π = B * E ∧
      ((E).support ≤ B.support ↔ D.IsNodeOfReducedBoundary s p) := by
  intro _ _ hcan D
  have : Smooth s := SmoothOfRelativeDimension.smooth 2 _
  have : IsNoetherian X := isNoetherian_of_finiteType s
  have : IsReduced B.subscheme := hnodal.isReduced
  by_cases hE : (E).support ≤ B.support
  · obtain ⟨hD, hred, hcanD, htotal, hcases⟩ := hB.anticanonical_boundary_point_blowdown k hp hcan
    obtain ⟨hm, -, hstrict⟩ := hcases.resolve_left (fun h ↦ h.2.1 hE)
    have hs : AtWorstNodalOfRelativeDimensionOne ((strict(D) * E).subschemeι ≫ π ≫ s) :=
      hstrict.symm ▸ hnodal
    obtain ⟨-, hcount, -⟩ := hD.ncard_strictTransform_inter_exceptional_of_nodal k hp hs
    have hncard : ((strict(D) ⊔ E).support : Set (I).blowup).ncard = 2 := by
      rw [hm, ENat.toNat_ofNat] at hcount
      exact hcount
    have hattach : ¬ (((strict(D)).support : Set (I).blowup) ∩
        ((E).support : Set (I).blowup)).Subsingleton := by
      intro h
      have hle := (Set.ncard_le_one h.finite).mpr h
      rw [← Closeds.coe_inf, ← support_sup, hncard] at hle
      omega
    have hnode (q : D.subscheme) (hq : D.subschemeι q = p) :=
      hD.isNodeAt_of_stalkOrder_eq_two_of_two_exceptional_attachments (k := k) q hq hp hm hattach
    have hnodalD := atWorstNodalOfRelativeDimensionOne_of_pointBlowdown htotal hnodal hp hnode
    have hmD : D.stalkOrder p = 2 := hm
    have hpD := (D.one_le_stalkOrder_iff p).mp (by rw [hmD]; decide)
    obtain ⟨q, hq⟩ := D.range_subschemeι.ge hpD
    have hnodeD := (D.isNodeOfReducedBoundary_iff_of_isReduced s p).mpr ⟨q, hq, hnode q hq⟩
    exact ⟨hD, hcanD, hnodalD, htotal, iff_of_true hE hnodeD⟩
  · obtain ⟨hD, hcanD, hnodalD, hm, htotal, -⟩ :=
      hB.internalBlowdown_of_anticanonical k hp hE hnodal hcan
    refine ⟨hD, hcanD, hnodalD, htotal, iff_of_false hE fun hn ↦ ?_⟩
    have htwo := hD.stalkOrder_eq_if_isNodeOfReducedBoundary hnodalD
      (mem_support_of_isNodeOfReducedBoundary hn)
    have hn' : (B.map π).IsNodeOfReducedBoundary s p := hn
    simp only [hn', ite_true, hm] at htwo
    exact (by decide : (1 : ℕ∞) ≠ 2) htwo

end AlgebraicGeometry.Scheme.IdealSheafData
