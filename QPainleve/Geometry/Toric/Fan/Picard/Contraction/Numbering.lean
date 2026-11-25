/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.Geometry.Toric.Fan.Boundary.Numbering
public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Picard.Contraction.Recovery

/-!
# Numbered toric models of internal contractions

An internal contraction whose base is a toric pair recovers an ordered toric
blowup. The numbering of the strict boundary determines the numbering of the
toric rays, with the same ordered branches and the corresponding Picard
classes. This is the comparison of the contracted models in the proof of
[Gross, Hacking and Keel, Theorem 1.8](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open QPainleve (BlowupTower)
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {X Y W : Scheme} {n m : ℕ} [NeZero m]
  {T : BlowupTower X n W}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "I[" h "]" => Fan.boundaryIdeal Φ (IsComplete.nonempty_cones h)
local notation "C[" h "]" => subscheme I[h]

variable [X.Over S] [Y.Over S] [IsLocallyNoetherian Y]
  [∀ y : Y, IsDomain (Y.presheaf.stalk y)]
  [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
  {D : Y.IdealSheafData} [PrestableFamily (D.subscheme ↘ S)]
  {γ : Type*} {p : γ → (D.subscheme ↘ S).smoothLocus}

/-- Recover the ordered toric model of a contraction to a specified toric pair,
numbered by the given cycle on the strict boundary. The comparison preserves
the contraction, the labeled total exceptional classes, and both branches at
each numbered node. The recovered frame is positive in the given cyclic order,
and each numbered boundary class pulls back to the strict class of the
corresponding ray. -/
theorem exists_numbered_toric_model_of_boundary_contraction
    (b : Module.Basis (Fin 2) ℤ N) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (A : Scheme.NodalCycleNumbering p m) (hD : D.IsEffectiveCartier)
    {E : X.IdealSheafData} [LocallyOfFinitePresentation (E.subschemeι ≫ X ↘ S)]
    (hT : T.IsClosedPointTower X) (d : Y ≅ W) (a : X ≅ Φ.algebraicRealization)
    (ha : a.hom ≫ Φ.algebraicRealizationStructureMap = X ↘ S)
    (hB : (I[hc]).comap a.hom = E)
    (hf : (d.hom ≫ T.toBase).IsOver S)
    (v : D.subscheme ≅ E.subscheme) (hv : v.hom ≫ E.subschemeι = D.subschemeι ≫ d.hom ≫ T.toBase)
    (hinj : Function.Injective hT.baseCenter)
    (hcenters : ∀ j, ∃ q : E.subscheme, E.subschemeι q = hT.baseCenter j ∧
      q ∈ (E.subschemeι ≫ X ↘ S).smoothLocus) :
    let := hc.nonempty_cones
    ∃ (hpre : PrestableFamily (C[hc] ↘ S)) (b' : Module.Basis (Fin 2) ℤ N)
      (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ),
      let := hpre
      let M := internalBlowupTower b' s c
      ∃ (e : M.1 ≅ Y) (eB : C[hc] ≅ D.subscheme) (hover : eB.hom.IsOver S)
        (B : Scheme.NodalCycleNumbering (Empty.elim : Empty → (C[hc] ↘ S).smoothLocus) m),
        let := hover
        let u := Φ.rayEquivOfNodalCycleNumbering hΦ B
        (b' = b ∨ b' = b.reindex (Equiv.swap 0 1)) ∧
        (∀ j, b'.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1) ∧
        (∀ j, ∃ σ : {σ : Φ.cones // Nat.card (ToricRay σ.val) = 2},
          (u j).toCone ≤ σ.val ∧ (u (j + 1)).toCone ≤ σ.val ∧
          (I[hc]).subschemeι ((C[hc]).dualGraphEdgeEquiv Empty.elim (B.edge j)).val =
            Φ.distinguishedPointHom σ.val (IsLocalRing.closedPoint ℂ)) ∧
        IsLift a T M.2.toTower (d.symm ≪≫ e.symm) ∧
        e.hom ≫ (Y ↘ S) = M.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
        eB.hom ≫ D.subschemeι = M.2.boundaryι ≫ e.hom ∧
        D.comap e.hom = M.2.boundaryι.ker ∧
        eB.boundaryCycleAction B A = 1 ∧
        (∀ j, pullback e.hom (pullback d.hom (T.exceptionalClass j)) =
          M.2.toTower.exceptionalClass j) ∧
        ∀ j, Additive.ofMul (pullback e.hom
            (primeDivisorClass (D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j)))) =
          strictRayBoundaryClass hΦ ((Module.finrank_eq_card_basis b').trans (Fintype.card_fin 2))
            M.2.toTower (isClosedPointTower_internalBlowupTower b' s c) (u j) := by
  let := hc.nonempty_cones
  let := hf
  have hDbase : D.subschemeι ≫ (d.hom ≫ T.toBase) ≫ (X ↘ S) = D.subscheme ↘ S := by
    rw [comp_over (d.hom ≫ T.toBase) S, D.over_eq_subschemeι_comp]
  obtain ⟨z, hz⟩ := (I[hc]).exists_iso_of_comap_eq_ker a E.subschemeι
    (hB.trans E.ker_subschemeι.symm)
  let eB := z.symm ≪≫ v.symm
  have hBbase : eB.hom ≫ D.subschemeι ≫ d.hom ≫ T.toBase ≫ a.hom = (I[hc]).subschemeι := by
    simp only [eB, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← reassoc_of% hv, Iso.inv_hom_id_assoc, ← hz, Iso.inv_hom_id_assoc]
  let : eB.hom.IsOver S := ⟨by
    rw [(I[hc]).over_eq_subschemeι_comp, Φ.algebraicRealization_over, ← reassoc_of% hBbase,
      ha, ← Category.assoc d.hom, hDbase]⟩
  let : PrestableFamily (C[hc] ↘ S) := by
    rw [← comp_over eB.hom S]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily)
      eB.hom _).2 inferInstance
  let : eB.symm.hom.IsOver S := inferInstanceAs (eB.inv.IsOver S)
  let B := eB.symm.mapNodalCycleNumbering A (q := Empty.elim)
  have hact : eB.boundaryCycleAction B A = 1 := by
    simpa only [Iso.symm_symm_eq, B, Iso.boundaryCycleAction_mapNodalCycleNumbering, inv_one]
      using eB.symm.boundaryCycleAction_symm A B
  -- Read the centers in the frame oriented by the transported boundary numbering.
  obtain ⟨b', hb', hpos, hnodes⟩ :=
    Φ.exists_positive_ray_numbering_of_nodalCycleNumbering b hΦ hc B
  obtain ⟨s, c, e, eB', hLift, hbase, heB, heD, hexc⟩ :=
    exists_ordered_toric_model_of_boundary_contraction b' hΦ hc (X ↘ S)
      hT d a ha hB v hv hinj hcenters
  let M := internalBlowupTower b' s c
  have hproj : e.hom ≫ d.hom ≫ T.toBase ≫ a.hom = M.2.toTower.toBase := by
    rw [← hLift.hom_toBase]
    simp only [M, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  -- Both boundary isomorphisms identify the same closed immersion into the toric base.
  have heq : eB' = eB := by
    apply Iso.ext
    have hmono : Mono (D.subschemeι ≫ d.hom ≫ T.toBase ≫ a.hom) := by
      rw [← reassoc_of% hv, ← hz]
      infer_instance
    apply (cancel_mono (D.subschemeι ≫ d.hom ≫ T.toBase ≫ a.hom)).mp
    rw [hBbase, reassoc_of% heB, hproj, WithBoundary.boundaryι_toBase]
  have hOver : e.hom ≫ (Y ↘ S) = M.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap := by
    rw [← hbase, ← Category.assoc d.hom, comp_over (d.hom ≫ T.toBase) S]
  have hboundary : eB.hom ≫ D.subschemeι = M.2.boundaryι ≫ e.hom := heq ▸ heB
  refine ⟨inferInstance, b', s, c, e, eB, inferInstance, B, hb', hpos, hnodes, hLift, hOver,
    hboundary, heD, hact, hexc, fun j ↦ ?_⟩
  have hj : eB.hom (B.componentGenericPoint j) = A.componentGenericPoint j := by
    simpa only [hact, map_one, Equiv.Perm.one_apply] using eB.apply_componentGenericPoint B A j
  have hcomponent := boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering hΦ B j
  exact pullback_numbered_boundaryPrime_eq_strictRayBoundaryClass b' hΦ s c B A hD e eB
    hboundary _ j j hcomponent.symm hj

end TauCeti.Toric.Fan
