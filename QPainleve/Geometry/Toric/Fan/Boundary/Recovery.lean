/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.Geometry.Toric.Fan.Boundary.SmoothPoint
public import QPainleve.Geometry.Toric.Fan.InternalBlowup

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Recovery
import QPainleve.AlgebraicGeometry.Blowup.Tower.DistinctCentres
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.FunctionField

/-!
# Recovering ordered internal models over a toric surface

After contracting a marked disjoint exceptional configuration onto a toric pair,
the projected points recover the ordered binomial centers. The resulting
identification lifts through the specified tower, thereby preserving the full
transforms of the exceptional classes and pullbacks from the base. Its boundary
embedding is the given lift of the toric boundary.

This is the passage from the contracted curves to a toric model in the proof of
[Gross, Hacking and Keel, Theorem 1.8][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N)
  {X Y : Scheme} {n : ℕ} {T : BlowupTower X n Y}

local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "D[" hc "]" => Φ.boundaryIdeal (IsComplete.nonempty_cones hc)
local notation "centerIdeal[" hc "," a "]" =>
  Scheme.IdealSheafData.map (Subtype.val (Ray.internalCenter (h₀ := IsComplete.nonempty_cones hc)
    b (Prod.fst a) (Prod.snd a))) (Scheme.IdealSheafData.subschemeι D[hc])
local notation "model[" hc "," a "]" =>
  internalBlowupTower (h₀ := IsComplete.nonempty_cones hc) b
    (Prod.fst ∘ a) (Prod.snd ∘ a)

private theorem baseCenter_internalBlowupTower_eq (hc : Φ.IsComplete)
    (a : Fin n → Φ.Ray × ℂˣ) (q : Fin n → Φ.algebraicRealization)
    (ha : ∀ j, centerIdeal[hc,a j] = (Φ.algebraicRealization.fromSpecResidueField (q j)).ker)
    (hA : IsClosedPointTower Φ.algebraicRealization (model[hc,a]).2.toTower) :
    ∀ j, hA.baseCenter j = q j := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  have hpt (j : Fin n) : ∃ p : (D[hc]).subscheme,
      ((a j).1.internalCenter b (a j).2).val = ((D[hc]).subscheme.fromSpecResidueField p).ker := by
    rw [Ray.internalCenter_val]
    obtain ⟨p, -, hp⟩ := (a j).1.exists_closedPoint_ker_binomialCenterOnBoundary rankTwo
      (b.detDualEquiv_self _) ((a j).1.surjective_detCharacter b) (a j).2
    exact ⟨p, hp⟩
  choose p hp using hpt
  -- The projected-center formula is stated for the underlying boundary tower.
  revert hA
  rw [internalBlowupTower_eq_alongBoundary]
  intro hA j
  have hproj := hA.baseCenter_alongBoundary p hp j
  refine hproj.trans (Scheme.ker_fromSpecResidueField_inj.mp ?_)
  rw [← (D[hc]).subschemeι.map_ker_fromSpecResidueField, ← hp j]
  exact ha j

/-- An ordered tower with distinct projected centers in the smooth toric boundary
is the ordered internal blowup model of the uniquely recovered ray and parameter
at each label. The isomorphism lifts the specified toric identification through
the towers, so the original labels give the total exceptional classes. It sends
the given lift of the toric boundary to the strict boundary of the model. -/
theorem existsUnique_ordered_toric_model_of_disjoint_blowup_tower
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (hT : IsClosedPointTower X T)
    (e : X ≅ Φ.algebraicRealization) (hinj : Function.Injective hT.baseCenter)
    (hmem : ∀ j, e.hom (hT.baseCenter j) ∈ (D[hc]).support)
    (hn : ∀ j, ¬ (D[hc]).IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap
      (e.hom (hT.baseCenter j)))
    (f : (D[hc]).subscheme ⟶ Y)
    (hf : f ≫ T.toBase ≫ e.hom = (D[hc]).subschemeι) :
    ∃! a : Fin n → Φ.Ray × ℂˣ,
      (∀ j, centerIdeal[hc,a j] =
        (Φ.algebraicRealization.fromSpecResidueField (e.hom (hT.baseCenter j))).ker) ∧
      ∃! g : Y ≅ (model[hc,a]).1, IsLift e T (model[hc,a]).2.toTower g ∧
        f ≫ g.hom = (model[hc,a]).2.boundaryι := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion e.hom
  have hparam (j : Fin n) := existsUnique_internalCenter_of_mem_boundary_of_not_isNode b hΦ hc
    (by simpa only [Set.image_singleton] using
      e.hom.isClosedEmbedding.isClosedMap _ (hT.isClosed_baseCenter j)) (hmem j) (hn j)
  simp only [ExistsUnique] at hparam
  choose a ha huniq using hparam
  let A := model[hc,a]
  let hA := isClosedPointTower_internalBlowupTower b (Prod.fst ∘ a) (Prod.snd ∘ a)
  have hproj := baseCenter_internalBlowupTower_eq b hc a (e.hom ∘ hT.baseCenter) ha hA
  obtain ⟨g, hg, hgu⟩ := hT.existsUnique_isLift_of_baseCenter_eq hA e hinj
    (fun j ↦ (hproj j).symm)
  refine ⟨a, ⟨ha, g, ⟨hg, ?_⟩, fun _ hg' ↦ hgu _ hg'.1⟩,
    fun a' ha' ↦ funext fun j ↦ huniq j _ (ha'.1 j)⟩
  have hcomm : (f ≫ g.hom) ≫ A.2.toTower.toBase = (D[hc]).subschemeι := by
    rw [Category.assoc, hg.hom_toBase, hf]
  have hsection (k : (D[hc]).subscheme ⟶ A.1)
      (hk : k ≫ A.2.toTower.toBase = (D[hc]).subschemeι) : k = A.2.boundaryι := by
    -- Rewriting the model also changes the type of the morphism into it.
    revert hk k
    dsimp only [A]
    rw [internalBlowupTower_eq_alongBoundary]
    exact eq_boundaryι_of_comp_toBase_alongBoundary _ _
  exact hsection _ hcomm

end TauCeti.Toric.Fan
