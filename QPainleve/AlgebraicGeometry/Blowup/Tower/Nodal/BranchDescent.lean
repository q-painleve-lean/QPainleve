/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Boundary
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.FixedBranches

import QPainleve.AlgebraicGeometry.Blowup.StrictTransform.Branches.Automorphism
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Restriction
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.Curves.SingularLocus.Smooth
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced

/-!
# Descending branch fixation through nodal blowup towers

If an automorphism lifts through a specified tower of nodal blowups and fixes
the branches of its reduced total boundary, it fixes the branches of the
original boundary. The attachments of the strict transform to each exceptional
divisor detect the branches at the contracted node.

This comparison is used in the toric reduction of [Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, Proposition 2.6][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace TauCeti.AlgebraicGeometry
open Scheme.Hom Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {k : Type u} [Field k] [PerfectField k]
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))]

variable [IsIntegral X] [IsNoetherian X] [QuasiCompact (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))] {D : X.IdealSheafData}
  (hD : D.IsEffectiveCartier)
  (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ (X ↘ Spec (.of k))))
  {e : X ≅ X} (he : e.hom ≫ (X ↘ Spec (.of k)) = (X ↘ Spec (.of k)))
  {d : D.subscheme ≅ D.subscheme} (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ e.hom)

include hD hN he hd in
private theorem fixes_branches_at_prefix {m : ℕ} {U : BlowupTower X m Y}
    (hU : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) U)
    {g : Y ≅ Y} (hg : IsLift e U U g)
    {J : Y.IdealSheafData} {p : Y} (hp : IsClosed ({p} : Set Y))
    (hJ : J = (Y.fromSpecResidueField p).ker)
    (hpN :
      (D.comap U.toBase).radical.IsNodeOfReducedBoundary (U.toBase ≫ X ↘ Spec (.of k)) p)
    (hcenter : J.comap g.hom = J)
    {P : J.blowup.IdealSheafData} (hP : P = (D.comap (U.snoc J).toBase).radical)
    {r : P.subscheme ≅ P.subscheme}
    (hr : r.hom ≫ P.subschemeι = P.subschemeι ≫ (J.blowupIso g hcenter).hom)
    (hNP : AtWorstNodalOfRelativeDimensionOne
      (P.subschemeι ≫ J.blowupToBase ≫ U.toBase ≫ X ↘ Spec (.of k)))
    (hrOver : r.hom ≫ P.subschemeι ≫ J.blowupToBase ≫ U.toBase ≫ X ↘ Spec (.of k) =
      P.subschemeι ≫ J.blowupToBase ≫ U.toBase ≫ X ↘ Spec (.of k))
    (hb : r.FixesNodalBranches _ hNP hrOver) :
    let Q := (D.comap U.toBase).radical
    ∃ (a : Q.subscheme ≅ Q.subscheme) (ha : a.hom ≫ Q.subschemeι = Q.subschemeι ≫ g.hom),
      a.FixesNodalBranches _ (hU.radical_comap_toBase hD hN).2
        (by rw [reassoc_of% ha, hg.hom_toBase_assoc, he]) := by
  let f := U.toBase ≫ (X ↘ Spec (.of k))
  let Q := (D.comap U.toBase).radical
  let : Y.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
    hU.isClosedPointTower.smoothOfRelativeDimension (X ↘ Spec (.of k))
  have : IsIntegral Y := hU.isClosedPointTower.isIntegral (X ↘ Spec (.of k))
  have : IsProper U.toBase := U.isProper_toBase
  have : QuasiCompact (Y ↘ Spec (.of k)) :=
    inferInstanceAs (QuasiCompact (U.toBase ≫ X ↘ Spec (.of k)))
  obtain ⟨hQ, hNQ⟩ := hU.radical_comap_toBase hD hN
  have : IsReduced Q.subscheme := hNQ.isReduced
  obtain ⟨q, hq, hqn⟩ := (Q.isNodeOfReducedBoundary_iff_of_isReduced _ _).mp hpN
  subst p
  obtain ⟨a, ha⟩ := D.exists_radicalComapSubschemeIso U.toBase hd hg.hom_toBase
  refine ⟨a, ha, ?_⟩
  let J' := vanishingIdeal (Closeds.mk (closure ({Q.subschemeι q} : Set Y)) isClosed_closure)
  have hJJ' : J = J' := hJ.trans (Y.ker_fromSpecResidueField_eq_vanishingIdeal (Q.subschemeι q))
  clear hJ
  subst J
  have hP' : P = (Q.comap J'.blowupToBase).radical := by
    rw [hP, toBase_snoc, comap_comp, ← vanishingIdeal_support,
      ← vanishingIdeal_support (I := Q.comap _), support_comap, support_comap Q]
    rfl
  clear hP
  subst P
  let : Q.subscheme.Over (Spec (.of k)) := ⟨Q.subschemeι ≫ f⟩
  let : a.hom.IsOver (Spec (.of k)) := ⟨((reassoc_of% ha) f).trans (congrArg (Q.subschemeι ≫ ·)
    (by dsimp only [f]; rw [hg.hom_toBase_assoc, he]))⟩
  have : SyntomicOfRelativeDimension 1 (Q.subscheme ↘ Spec (.of k)) := hNQ.syntomic
  have hsing := (Q.subscheme.mem_support_singularLocus_iff_notMem_smoothLocus q).mpr
    (((Q.subschemeι ≫ f).isNodeAt_iff_notMem_smoothLocus hNQ q).mp hqn)
  have hfix : a.hom q = q := by
    apply Q.subschemeι.injective
    have hpoint := congrArg (fun t : Q.subscheme ⟶ Y ↦ t q) ha
    simp only [Scheme.Hom.comp_apply] at hpoint
    rw [hpoint]
    have hS : (J'.support : Set Y) = {Q.subschemeι q} := by
      dsimp only [J']
      rw [coe_support_vanishingIdeal, Closeds.coe_mk, hp.closure_eq]
    have h := SetLike.ext'_iff.mp (congrArg support hcenter)
    rw [support_comap, Closeds.coe_preimage, hS] at h
    have hx : Q.subschemeι q ∈ g.hom ⁻¹' ({Q.subschemeι q} : Set Y) :=
      h.symm ▸ Set.mem_singleton _
    exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp hx)
  let : (Q.comap J'.blowupToBase).radical.subscheme.Over (Spec (.of k)) :=
    ⟨(Q.comap J'.blowupToBase).radical.subschemeι ≫ J'.blowupToBase ≫ f⟩
  let : r.hom.IsOver (Spec (.of k)) := ⟨hrOver⟩
  apply (a.fixesNodalBranches_iff _ hNQ _).mpr
  exact hQ.singularLocusBlowupIso_fixes_over_of_nodeBlowup hNQ hsing hp
    g a ha hfix r hNP hr rfl rfl ((r.fixesNodalBranches_iff _ hNP hrOver).mp hb)

include hD hN he hd in
private theorem fixes_nodal_branches_aux {n : ℕ} {T : BlowupTower X n Y}
    (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
    {g : Y ≅ Y} (hg : IsLift e T T g)
    {P : Y.IdealSheafData} (hP : P = (D.comap T.toBase).radical)
    {r : P.subscheme ≅ P.subscheme} (hr : r.hom ≫ P.subschemeι = P.subschemeι ≫ g.hom)
    (hNP : AtWorstNodalOfRelativeDimensionOne (P.subschemeι ≫ T.toBase ≫ (X ↘ Spec (.of k))))
    (hrOver : r.hom ≫ P.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k) =
      P.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k))
    (hb : r.FixesNodalBranches _ hNP hrOver) :
    d.FixesNodalBranches _ hN (by rw [reassoc_of% hd, he]) := by
  induction hT with
  | nil =>
    have : IsReduced D.subscheme := hN.isReduced
    have heq : P = D := by
      simpa only [toBase_nil, comap_id, D.isReduced_subscheme_iff_radical_eq.mp inferInstance]
        using hP
    clear hP
    subst P
    have hrd : r = d := by
      apply Iso.ext
      exact (cancel_mono D.subschemeι).mp (hr.trans (IsLift.nil_iff.mp hg ▸ hd.symm))
    subst r
    simpa only [toBase_nil, Category.id_comp] using hb
  | @snoc m Z U J hU p hp hJ hpN ih =>
    obtain ⟨g', hg', hcenter, rfl⟩ := IsLift.snoc_iff.mp hg
    have hN' : AtWorstNodalOfRelativeDimensionOne
        (P.subschemeι ≫ J.blowupToBase ≫ U.toBase ≫ X ↘ Spec (.of k)) := by
      simpa only [toBase_snoc, Category.assoc] using hNP
    obtain ⟨a, ha, hb'⟩ :=
      fixes_branches_at_prefix hD hN he hd hU hg' hp hJ
        (by simpa only [isNodeOfReducedBoundary_radical, Category.comp_id] using hpN)
        hcenter hP hr hN'
        (by simpa only [toBase_snoc, Category.assoc] using hrOver)
        (by simpa only [toBase_snoc, Category.assoc] using hb)
    exact ih hg' rfl ha _ _ hb'

include hD hN he hd in
/-- If an ordered lift through nodal blowups fixes all branches of the reduced total
boundary, the original automorphism fixes all branches of the original boundary. -/
theorem IsNodalBoundaryTower.fixes_nodal_branches_of_isLift {n : ℕ} {T : BlowupTower X n Y}
    (hT : IsNodalBoundaryTower D (X ↘ Spec (.of k)) (𝟙 X) T)
    {g : Y ≅ Y} (hg : IsLift e T T g)
    {r : (D.comap T.toBase).radical.subscheme ≅ (D.comap T.toBase).radical.subscheme}
    (hr : r.hom ≫ (D.comap T.toBase).radical.subschemeι =
      (D.comap T.toBase).radical.subschemeι ≫ g.hom)
    (hfix : r.FixesNodalBranches
      ((D.comap T.toBase).radical.subschemeι ≫ T.toBase ≫ X ↘ Spec (.of k))
        (hT.radical_comap_toBase hD hN).2
        (by rw [reassoc_of% hr, hg.hom_toBase_assoc, he])) :
    d.FixesNodalBranches _ hN (by rw [reassoc_of% hd, he]) :=
  fixes_nodal_branches_aux hD hN he hd hT hg rfl hr (hT.radical_comap_toBase hD hN).2
    (by rw [reassoc_of% hr, hg.hom_toBase_assoc, he]) hfix

end QPainleve.BlowupTower
