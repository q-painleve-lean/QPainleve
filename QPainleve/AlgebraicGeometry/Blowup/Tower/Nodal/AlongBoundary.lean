/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Boundary
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic

import QPainleve.AlgebraicGeometry.Blowup.Disjoint
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import TauCeti.AlgebraicGeometry.Blowup.Restriction

/-!
# Nodal blowup towers after internal blowups

A tower of blowups at nodes of the reduced boundary can be pulled back through an
ordered sequence of Cartier centers on the smooth part of the boundary. Each node
lifts to a node of the reduced total transform of the new strict boundary. The
comparison is cartesian on the actual schemes.

The two-step comparison uses the fiber product of blowups at disjoint centers.
For internal and corner blowups of anticanonical cycles, see Gross, Hacking and Keel,
[*Moduli of surfaces with an anti-canonical cycle*, Definition 1.2][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open Scheme.IdealSheafData

universe u

namespace QPainleve.BlowupTower

variable {K X Y Y' : Scheme.{u}} {s : X ⟶ K} {D : X.IdealSheafData} {n : ℕ}

namespace IsNodalBoundaryTower

private theorem exists_isPullback_disjoint_step (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : Y.IdealSheafData) (h : Disjoint ((I.comap f).support : Set Y) (J.support : Set Y))
    (e : Y' ≅ (I.comap f).blowup) :
    let g := e.hom ≫ (I.comap f).blowupToBase
    ∃ e' : (J.comap g).blowup ≅ (I.comap (J.blowupToBase ≫ f)).blowup,
      IsPullback (e'.hom ≫ (I.comap (J.blowupToBase ≫ f)).blowupToBase)
        (J.comap g).blowupToBase J.blowupToBase g := by
  let F := I.comap f
  let g := e.hom ≫ F.blowupToBase
  let E := J.comap F.blowupToBase
  let a : (J.comap g).blowup ≅ E.blowup :=
    E.blowupIso e (J.comap_comp e.hom F.blowupToBase).symm
  let b := F.blowupCommOfDisjoint J h
  let H := I.comap (J.blowupToBase ≫ f)
  let c : (F.comap J.blowupToBase).blowup ≅ H.blowup :=
    H.blowupIso (Iso.refl _) (by simp [H, F, comap_comp])
  have hp : IsPullback (J.blowupMap F.blowupToBase) E.blowupToBase J.blowupToBase F.blowupToBase :=
    (J.isPullback_blowupMap_of_disjoint F h.symm).flip
  have hg : (a ≪≫ b ≪≫ c).hom ≫ H.blowupToBase = a.hom ≫ J.blowupMap F.blowupToBase := by
    simp only [Iso.trans_hom, Category.assoc, c, blowupIso_hom_blowupToBase,
      Iso.refl_hom, Category.comp_id, b, blowupCommOfDisjoint_hom_blowupToBase]
  refine ⟨a ≪≫ b ≪≫ c, ?_⟩
  rw [hg]
  exact hp.of_iso' a (Iso.refl _) e (Iso.refl _) (by simp) (by simp [a, g, F])
    (by simp) (by simp [F])

private theorem isNode_of_comap_eq_on_exceptionalCompl (I : X.IdealSheafData)
    (D' : I.blowup.IdealSheafData)
    (hD' : let U : I.blowup.Opens := (I.comap I.blowupToBase).support.compl
      D'.comap U.ι = (D.comap I.blowupToBase).comap U.ι)
    {W Z : Scheme.{u}} {f : W ⟶ X} {r : Z ⟶ I.blowup} {g : Z ⟶ W}
    (hcomm : g ≫ f = r ≫ I.blowupToBase) {z : Z}
    (hz : f (g z) ∉ I.support) (hgz : g z ∈ g.isoLocus)
    (hn : (D.comap f).IsNodeOfReducedBoundary (f ≫ s) (g z)) :
    (D'.comap r).IsNodeOfReducedBoundary (r ≫ I.blowupToBase ≫ s) z := by
  let U : I.blowup.Opens := (I.comap I.blowupToBase).support.compl
  let V : Z.Opens := r ⁻¹ᵁ U
  have hzr : I.blowupToBase (r z) = f (g z) := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun m : Z ⟶ X ↦ m z) hcomm.symm
  have hzV : z ∈ V := by
    dsimp only [V, U]
    rw [r.mem_preimage, compl_support_comap, I.blowupToBase.mem_preimage,
      ← SetLike.mem_coe, Closeds.coe_compl, hzr]
    exact hz
  let zv : V := ⟨z, hzV⟩
  have heq : ((D.comap f).comap g).comap V.ι = (D'.comap r).comap V.ι := by
    rw [← comap_comp (D.comap f), ← comap_comp, Category.assoc, hcomm,
      ← Category.assoc, ← morphismRestrict_ι r U, comap_comp, comap_comp,
      ← hD', ← comap_comp, morphismRestrict_ι, comap_comp]
  have hlocal := ((D.comap f).isNodeOfReducedBoundary_comap_iff_of_mem_isoLocus _ g hgz).mpr hn
  rw [← Category.assoc, hcomm, Category.assoc] at hlocal
  have hlocal' := (((D.comap f).comap g).isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion
    _ V.ι zv).mpr hlocal
  rw [heq] at hlocal'
  exact ((D'.comap r).isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion _ V.ι zv).mp hlocal'

private theorem exists_isPullback_blowup_aux {T : BlowupTower X n Y} [IsLocallyNoetherian X]
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (I : X.IdealSheafData)
    (hI : ∀ x ∈ (I.support : Set X), ¬ D.IsNodeOfReducedBoundary s x)
    (D' : I.blowup.IdealSheafData)
    (hD' : let U : I.blowup.Opens := (I.comap I.blowupToBase).support.compl
      D'.comap U.ι = (D.comap I.blowupToBase).comap U.ι) :
    ∃ (Z : Scheme.{u}) (R : BlowupTower I.blowup n Z) (e : Z ≅ (I.comap T.toBase).blowup),
      IsNodalBoundaryTower D' (I.blowupToBase ≫ s) (𝟙 I.blowup) R ∧
      IsPullback (e.hom ≫ (I.comap T.toBase).blowupToBase) R.toBase T.toBase I.blowupToBase := by
  induction hT with
  | nil =>
    let e : I.blowup ≅ (I.comap (BlowupTower.nil (X := X)).toBase).blowup :=
      (I.comap (BlowupTower.nil (X := X)).toBase).blowupIso (Iso.refl _) (by simp)
    refine ⟨_, .nil, e, .nil, ?_⟩
    simp only [toBase_nil]
    exact IsPullback.of_vert_isIso ⟨by simp [e]⟩
  | @snoc n Y T J hT p hp hJ hP ih =>
    obtain ⟨Z, R, e, hR, he⟩ := ih
    let F := I.comap T.toBase
    let g := e.hom ≫ F.blowupToBase
    have hNp : (D.comap T.toBase).IsNodeOfReducedBoundary (T.toBase ≫ s) p := by
      simpa only [Category.comp_id] using hP
    have hpAvoid : T.toBase p ∉ I.support := by
      intro hpI
      have hn := hI _ hpI
      have hi : T.toBase p ∈ T.toBase.isoLocus := by
        by_contra hc
        apply hn
        exact centre_subset_nodes hT (by
          simpa only [Scheme.Hom.centre_def, Set.mem_compl_iff, SetLike.mem_coe] using hc)
      exact hn ((D.isNodeOfReducedBoundary_comap_iff_of_mem_isoLocus s T.toBase hi).mp hNp)
    have hpF : p ∉ F.support := by
      dsimp only [F]
      rwa [support_comap, ← SetLike.mem_coe, Closeds.coe_preimage]
    have hd : Disjoint (F.support : Set Y) (J.support : Set Y) := by
      rw [hJ, Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
      exact Set.disjoint_singleton_right.mpr hpF
    have hFg : IsIso (F.blowupToBase ∣_ F.support.compl) :=
      F.isIso_blowupToBase_restrict_compl_support
    have hIso : IsIso (g ∣_ F.support.compl) := by
      let V := F.blowupToBase ⁻¹ᵁ F.support.compl
      have hE : IsIso (e.hom ∣_ V) := e.hom.isIso_morphismRestrict_of_le_opensRange
        (by rw [Scheme.Hom.opensRange_of_isIso]; exact le_top)
      exact (morphismRestrict_comp e.hom F.blowupToBase F.support.compl).symm ▸
        IsIso.comp_isIso' hE hFg
    have hpi : p ∈ g.isoLocus := g.le_isoLocus_iff.mpr hIso hpF
    obtain ⟨q, hq, hqg, hqJ⟩ :=
      g.exists_comap_ker_fromSpecResidueField_of_isIso_morphismRestrict p hp _ hpi
    have hqNode := isNode_of_comap_eq_on_exceptionalCompl I D' hD' he.w
      (hqg.symm ▸ hpAvoid) (hqg.symm ▸ hpi) (hqg.symm ▸ hNp)
    rw [toBase_snoc]
    obtain ⟨e', he'⟩ := exists_isPullback_disjoint_step I T.toBase J hd e
    refine ⟨_, R.snoc (J.comap g), e', hR.snoc q hq (hJ ▸ hqJ) ?_, ?_⟩
    · simpa only [Category.comp_id, Category.assoc] using hqNode
    · simpa only [toBase_snoc] using he'.paste_vert he

/-- Pull a nodal tower back along a blowup with center avoiding the nodes of the
original reduced boundary. The new boundary may be any ideal agreeing with the
total transform away from the exceptional divisor, in particular the strict transform. -/
theorem exists_isPullback_blowup_of_avoids_nodes {T : BlowupTower X n Y} [IsLocallyNoetherian X]
    (hT : IsNodalBoundaryTower D s (𝟙 X) T) (I : X.IdealSheafData)
    (hI : ∀ x ∈ (I.support : Set X), ¬ D.IsNodeOfReducedBoundary s x)
    (D' : I.blowup.IdealSheafData)
    (hD' : let U : I.blowup.Opens := (I.comap I.blowupToBase).support.compl
      D'.comap U.ι = (D.comap I.blowupToBase).comap U.ι) :
    ∃ (Z : Scheme.{u}) (R : BlowupTower I.blowup n Z) (g : Z ⟶ Y),
      IsNodalBoundaryTower D' (I.blowupToBase ≫ s) (𝟙 I.blowup) R ∧
      IsPullback g R.toBase T.toBase I.blowupToBase := by
  obtain ⟨Z, R, e, hR, hp⟩ := exists_isPullback_blowup_aux hT I hI D' hD'
  exact ⟨Z, R, _, hR, hp⟩

variable {B : Scheme.{u}} {m : ℕ}

/-- Pull back a nodal tower through the ordered blowups of Cartier centers on a fixed
reduced boundary. The centers can repeat, and each must avoid the original nodes. The
result is a nodal tower for the final strict boundary, with the same number of nodal
blowups and a cartesian square over the original scheme. -/
theorem exists_isPullback_alongBoundary_of_avoids_nodes [IsLocallyNoetherian X]
    (i : B ⟶ X) [IsClosedImmersion i] [IsReduced B] {T : BlowupTower X n Y}
    (hT : IsNodalBoundaryTower i.ker s (𝟙 X) T)
    (J : Fin m → {A : B.IdealSheafData // A.IsEffectiveCartier})
    (hJ : ∀ j p, p ∈ ((J j).val.support : Set B) → ¬ (i ≫ s).IsNodeAt p) :
    let U := alongBoundary i J
    ∃ (Z : Scheme.{u}) (R : BlowupTower U.1 n Z) (g : Z ⟶ Y),
      IsNodalBoundaryTower U.2.boundaryι.ker (U.2.toTower.toBase ≫ s) (𝟙 U.1) R ∧
      IsPullback g R.toBase T.toBase U.2.toTower.toBase := by
  dsimp only
  induction m with
  | zero =>
    rw [alongBoundary_zero i]
    simp only [WithBoundary.toTower_nil, toBase_nil, WithBoundary.boundaryι_nil, Category.id_comp]
    exact ⟨Y, T, 𝟙 Y, hT, IsPullback.of_horiz_isIso ⟨by simp⟩⟩
  | succ m ih =>
    obtain ⟨W, L, f, hL, hf⟩ := ih (fun j ↦ J j.castSucc) (fun j ↦ hJ j.castSucc)
    let U := alongBoundary i (fun j : Fin m ↦ J j.castSucc)
    let A := J (Fin.last m)
    let I := A.val.map U.2.boundaryι
    let U' := U.2.snoc A.val A.property
    let : IsProper U.2.toTower.toBase := U.2.toTower.isProper_toBase
    have : IsLocallyNoetherian U.1 :=
      LocallyOfFiniteType.isLocallyNoetherian U.2.toTower.toBase
    have hI (x : U.1) (hx : x ∈ (I.support : Set U.1)) :
        ¬ U.2.boundaryι.ker.IsNodeOfReducedBoundary (U.2.toTower.toBase ≫ s) x := by
      have hc := U.2.boundaryι.isClosedEmbedding
      dsimp only [I] at hx
      rw [support_map, Closeds.coe_closure, (hc.isClosedMap _ A.val.support.isClosed).closure_eq]
        at hx
      obtain ⟨p, hp, rfl⟩ := hx
      intro hNode
      obtain ⟨q, hq, hqNode⟩ := (U.2.boundaryι.isNodeOfReducedBoundary_ker_iff _ _).mp hNode
      have heq : q = p := hc.injective hq
      subst q
      exact hJ (Fin.last m) p hp (by simpa using hqNode)
    have hboundary :
        let V : I.blowup.Opens := (I.comap I.blowupToBase).support.compl
        U'.boundaryι.ker.comap V.ι =
          (U.2.boundaryι.ker.comap I.blowupToBase).comap V.ι := by
      dsimp only [U']
      rw [WithBoundary.ker_boundaryι_snoc, ker_blowupMap_eq_ker_blowupMap_subschemeι,
        comap_ker_blowupMap_subschemeι_exceptionalCompl]
    obtain ⟨Z, R, g, hR, hg⟩ :=
      exists_isPullback_blowup_of_avoids_nodes hL I hI U'.boundaryι.ker hboundary
    rw [alongBoundary_succ i]
    refine ⟨Z, R, g ≫ f, ?_, ?_⟩
    · simpa only [WithBoundary.toTower_snoc, toBase_snoc, Category.assoc] using hR
    · simpa only [WithBoundary.toTower_snoc, toBase_snoc] using hg.paste_horiz hf

end IsNodalBoundaryTower

end QPainleve.BlowupTower
