/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.Geometry.Toric.Fan.Boundary.PositiveRefinement
public import QPainleve.SignedClusterModularGroup.Realization.Agreement

import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.Geometry.Toric.Fan.Boundary.Node
import QPainleve.Geometry.Toric.Fan.Picard.Subdivision
import QPainleve.Geometry.Toric.Fan.Subdivision.NodalRefinement

/-!
# Refining marked toric presentations

A regular refinement of the toric fan gives another presentation of the same
marked surface. The refined internal centers lie on the lifted rays in the
original order, and the fixed Picard coordinates pull back the toric class and
retain every total exceptional coefficient. The construction uses the ordered
model comparison of `Fan.IsSubdivision.exists_nodal_refinement_internalBlowupTower`.
For ordered toric presentations and refinements by boundary nodes, see
[Gross, Hacking and Keel, Definition 1.2 and the paragraph following it][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S1
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative
open QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup.ContractedToricFiber

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ : Fan i} [hΦ₀ : Nonempty Φ.cones] [hΨ₀ : Nonempty Ψ.cones]
  {r m n : ℕ} [NeZero m] [NeZero n]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray}
  {hΦ : Φ.IsRegular}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "D[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "Pic[" Φ "," r "]" =>
  Additive (LineBundleClass (Fan.algebraicRealization Φ)) × (Fin r → ℤ)

variable [PrestableFamily (D[Φ,hΦ₀] ↘ S)]
  {γ δ : Type*} {a : γ → (D[Φ,hΦ₀] ↘ S).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m}
  {o : ZMod m} {J : L →ₗ[ℤ] Pic[Φ,r]}
  {c : Multiplicative (Fin r → ℤ) →* ℂˣ}
  {M : MarkedSurface ℂ n B (Spec (CommRingCat.of (LaurentRing ℂ (Fin r))))}
  (p : ContractedToricFiber b s hΦ T o J c M) (h : Ψ.IsSubdivision Φ)

local notation "centers" c:arg => (fun j ↦ c (ofAdd (Pi.single j 1)))
local notation "A" => internalBlowupTower b s (centers c)
local notation "A'" => internalBlowupTower b (h.liftRay ∘ s) (centers c)
local notation "π" => toBase (WithBoundary.toTower (Sigma.snd (A)))
local notation "π'" => toBase (WithBoundary.toTower (Sigma.snd (A')))
local notation "f" => h.toFanHom.algebraicMap
local notation "β" => h.boundaryMap hΨ₀ hΦ₀
local notation "J'" => LinearMap.comp
  (LinearMap.prodMap (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive
    (LineBundleClass.pullbackHom (h.toFanHom.algebraicMap)))) LinearMap.id) J

open Scheme.RationalMap in
private theorem evaluation_eq_subdivision (hΨ : Ψ.IsRegular) (g : (A').1 ⟶ (A).1)
    [IsModification g] (hg : g ≫ π = π' ≫ f) :
    M.evaluation = contractedXEvaluation b (h.liftRay ∘ s) c hΨ (g ≫ p.projection) := by
  have : IsIntegral (A').1 := isIntegral_internalBlowupTower b (h.liftRay ∘ s) (centers c) hΨ
  have : IsModification π' :=
    isModification_internalBlowupTower_toBase b (h.liftRay ∘ s) (centers c) hΨ
  rw [p.evaluation_eq]
  simpa only [id_comp, compHom_id] using
    (comp_contractedXEvaluation_of_common_model b s c hΦ p.projection b (h.liftRay ∘ s)
      c hΨ (g ≫ p.projection) g (𝟙 _) (𝟙 _) (by simp) (𝟙 _) (by
        simp only [Category.id_comp, compHom_id, hg, ← Scheme.Hom.toRationalMap_compHom,
          ← comp_toRationalMap, comp_assoc, h.comp_xEvaluation])).symm

private theorem marked_pullback_subdivision (hΨ : Ψ.IsRegular) (g : (A').1 ⟶ (A).1)
    (hg : g ≫ π = π' ≫ f) (x : L) :
    (internalBlowupPicardMarking b (h.liftRay ∘ s) (centers c) hΨ).symm
      (Additive.ofMul (LineBundleClass.pullback (g ≫ p.projection) (M.picardMarking x).toMul)) =
      J' x := by
  have hx := congrArg (internalBlowupPicardMarking b s (centers c) hΦ) (p.marked_pullback x)
  simp only [LinearEquiv.apply_symm_apply] at hx
  apply (internalBlowupPicardMarking b (h.liftRay ∘ s) (centers c) hΨ).injective
  rw [LinearEquiv.apply_symm_apply, ← LineBundleClass.pullback_comp]
  have hx' := congrArg Additive.toMul hx
  rw [toMul_ofMul] at hx'
  rw [hx']
  simpa only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
    AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive, Function.comp_apply,
    LineBundleClass.pullbackHom_apply, ofMul_toMul, Prod.eta] using congrArg Additive.ofMul
    (h.pullback_internalBlowupPicardMarking b s (centers c) hΨ hΦ g hg (J x).1.toMul (J x).2)

section Numbering

variable [PrestableFamily (D[Ψ,hΨ₀] ↘ S)] {l : ℕ} [NeZero l]
  {a' : δ → (D[Ψ,hΨ₀] ↘ S).smoothLocus} {U : Scheme.NodalCycleNumbering a' l}
  {o' : ZMod l}

/-- The same contracted marked surface admits the refined presentation. Its contraction
factors through the original ordered model by a nodal tower, and its boundary map
is the composite of the subdivision and the original boundary map. -/
theorem exists_subdivision (hΨ : Ψ.IsRegular)
    (hU : (β).IsOrientedCycleSubdivision U T)
    (ho : β (U.componentGenericPoint o') = T.componentGenericPoint o) :
    ∃ (q : ContractedToricFiber b (h.liftRay ∘ s) hΨ U o' J' c M)
      (k : ℕ) (Y : Scheme) (R : BlowupTower (A).1 k Y) (e : (A').1 ≅ Y),
      IsNodalBoundaryTower (A).2.boundaryι.ker (π ≫ Φ.algebraicRealizationStructureMap)
        (𝟙 _) R ∧
      q.projection = e.hom ≫ R.toBase ≫ p.projection ∧ q.boundaryMap = β ≫ p.boundaryMap := by
  have : IsIntegral (A').1 := isIntegral_internalBlowupTower b (h.liftRay ∘ s) (centers c) hΨ
  have : IsModification π := isModification_internalBlowupTower_toBase b s (centers c) hΦ
  have : IsModification π' :=
    isModification_internalBlowupTower_toBase b (h.liftRay ∘ s) (centers c) hΨ
  obtain ⟨k, Y, R, e, hR, hcart, hD, hboundary⟩ :=
    h.exists_nodal_refinement_internalBlowupTower b hΨ hΦ s (centers c)
  let g := e.hom ≫ R.toBase
  have hg : g ≫ π = π' ≫ f := hcart.w
  have : IsIntegral (A).1 := isIntegral_internalBlowupTower b s (centers c) hΦ
  have := smoothOfRelativeDimension_internalBlowupTower b s (centers c) hΦ
  have : IsModification R.toBase :=
    hR.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two
      (π ≫ Φ.algebraicRealizationStructureMap)
  have : IsModification g := inferInstanceAs (IsModification (e.hom ≫ R.toBase))
  have hβ : (A').2.boundaryι ≫ g = β ≫ (A).2.boundaryι := hboundary
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  refine ⟨{
    projection := g ≫ p.projection
    projection_over := by
      rw [Category.assoc, p.projection_over, reassoc_of% hg,
        FanHom.algebraicMap_comp_algebraicRealizationStructureMap]
    support_comap := ?_
    boundaryMap := β ≫ p.boundaryMap
    boundary_comp := by rw [Category.assoc, p.boundary_comp, ← Category.assoc, ← hβ,
      Category.assoc]
    orientedSubdivision := hU.comp p.orientedSubdivision
    component_zero := by rw [Scheme.Hom.comp_apply, ho, p.component_zero]
    marked_pullback := marked_pullback_subdivision p h hΨ g hg
    evaluation_eq := evaluation_eq_subdivision p h hΨ g hg
  }, k, Y, R, e, hR, rfl, rfl⟩
  · rw [comap_comp, Scheme.IdealSheafData.support_comap, p.support_comap,
      ← Scheme.IdealSheafData.support_comap, ← hD,
      ← radical_comap_of_isOpenImmersion, support_radical, comap_comp]

end Numbering

local notation "Dₘ[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

private theorem exists_append_nodal_subdivision
    {j k : ℕ} {Y Z : Scheme} {T₀ : BlowupTower M.surface j Y}
    {R : BlowupTower (A).1 k Z} (e₀ : Y ≅ (A).1)
    (hT₀ : IsNodalBoundaryTower Dₘ[M] (M.surface ↘ S) (𝟙 _) T₀)
    (he₀ : p.projection = e₀.inv ≫ T₀.toBase)
    (hR : IsNodalBoundaryTower (A).2.boundaryι.ker
      (π ≫ Φ.algebraicRealizationStructureMap) (𝟙 _) R) :
    ∃ (W : Scheme) (T₁ : BlowupTower M.surface (j + k) W) (e₁ : W ≅ Z),
      IsNodalBoundaryTower Dₘ[M] (M.surface ↘ S) (𝟙 _) T₁ ∧
      T₁.toBase = e₁.hom ≫ R.toBase ≫ p.projection := by
  have hs : e₀.hom ≫ π ≫ Φ.algebraicRealizationStructureMap =
      T₀.toBase ≫ M.surface ↘ S := by
    simp only [← p.projection_over, he₀, Category.assoc, Iso.hom_inv_id_assoc]
  have hD : ((A).2.boundaryι.ker.comap e₀.hom).support = (Dₘ[M].comap T₀.toBase).support := by
    rw [Scheme.IdealSheafData.support_comap, ← p.support_comap,
      ← Scheme.IdealSheafData.support_comap, ← comap_comp, he₀, Iso.hom_inv_id_assoc]
  obtain ⟨W, V, d, hV, he, -⟩ := hT₀.exists_append_of_iso hR e₀ hs hD
  exact ⟨W, V, d, hV, by rw [he, he₀]⟩

/-- Refine all members of a marked family using a specified oriented subdivision
of its auxiliary boundary. The contractions retain the chosen numbering and the
component over the original origin. -/
private theorem subdivision_family_of_orientedCycleSubdivision {C : Type*}
    (χ : C → Multiplicative (Fin r → ℤ) →* ℂˣ)
    (P : C → MarkedSurface ℂ n B (Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))))
    (p : ∀ t, ContractedToricFiber b s hΦ T o J (χ t) (P t))
    (hΨ : Ψ.IsRegular)
    (hP : ∀ t, ∃ (Y : Scheme) (j : ℕ) (R : BlowupTower (P t).surface j Y)
        (e : Y ≅ (internalBlowupTower b s (centers(χ t))).1),
      IsNodalBoundaryTower Dₘ[P t] ((P t).surface ↘ S) (𝟙 _) R ∧
        (p t).projection = e.inv ≫ R.toBase)
    [PrestableFamily (D[Ψ,hΨ₀] ↘ S)] {l : ℕ} [NeZero l]
    {a' : δ → (D[Ψ,hΨ₀] ↘ S).smoothLocus}
    (U : Scheme.NodalCycleNumbering a' l) (o' : ZMod l)
    (hU : (β).IsOrientedCycleSubdivision U T)
    (ho' : β (U.componentGenericPoint o') = T.componentGenericPoint o) :
    ∀ t, ∃ (q : ContractedToricFiber b (h.liftRay ∘ s) hΨ U o' J' (χ t) (P t))
      (Y : Scheme) (j : ℕ) (R : BlowupTower (P t).surface j Y)
      (e : Y ≅ (internalBlowupTower b (h.liftRay ∘ s) (centers(χ t))).1),
      IsNodalBoundaryTower Dₘ[P t] ((P t).surface ↘ S) (𝟙 _) R ∧
      q.projection = e.inv ≫ R.toBase ∧ q.boundaryMap = β ≫ (p t).boundaryMap := by
  intro t
  obtain ⟨q, _, _, R, e, hR, hq, hb⟩ := (p t).exists_subdivision h hΨ hU ho'
  obtain ⟨_, _, _, e₀, hT₀, he₀⟩ := hP t
  obtain ⟨Y, R', e₁, hR', he₁⟩ := exists_append_nodal_subdivision (p t) e₀ hT₀ he₀ hR
  refine ⟨q, Y, _, R', e₁ ≪≫ e.symm, hR', ?_, hb⟩
  rw [Iso.trans_inv, Iso.symm_inv, he₁, Category.assoc, Iso.inv_hom_id_assoc, hq]

/-- Refine a fixed presentation over an arbitrary family of center parameters. The refined
numbering, component above the original origin, and Picard inclusion are common to all
members of the family. The extended nodal contraction presents each original marked
surface with the same X evaluation and the same ordered centers on the lifted rays. -/
theorem exists_subdivision_family {C : Type*} (χ : C → Multiplicative (Fin r → ℤ) →* ℂˣ)
    (P : C → MarkedSurface ℂ n B (Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))))
    (p : ∀ t, ContractedToricFiber b s hΦ T o J (χ t) (P t))
    (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
    (hP : ∀ t, ∃ (Y : Scheme) (j : ℕ) (R : BlowupTower (P t).surface j Y)
        (e : Y ≅ (internalBlowupTower b s (centers(χ t))).1),
      IsNodalBoundaryTower Dₘ[P t] ((P t).surface ↘ S) (𝟙 _) R ∧
        (p t).projection = e.inv ≫ R.toBase) :
    ∃ (hpre : PrestableFamily (D[Ψ,hΨ₀] ↘ S)) (l : ℕ) (_ : NeZero l),
      letI := hpre
      ∀ a' : δ → (D[Ψ,hΨ₀] ↘ S).smoothLocus,
        ∃ (U : Scheme.NodalCycleNumbering a' l) (o' : ZMod l),
          (β).IsOrientedCycleSubdivision U T ∧
          β (U.componentGenericPoint o') = T.componentGenericPoint o ∧
          ∀ t, ∃ (q : ContractedToricFiber b (h.liftRay ∘ s) hΨ U o' J' (χ t) (P t))
            (Y : Scheme) (j : ℕ) (R : BlowupTower (P t).surface j Y)
            (e : Y ≅ (internalBlowupTower b (h.liftRay ∘ s) (centers(χ t))).1),
            IsNodalBoundaryTower Dₘ[P t] ((P t).surface ↘ S) (𝟙 _) R ∧
            q.projection = e.inv ≫ R.toBase ∧ q.boundaryMap = β ≫ (p t).boundaryMap := by
  have hN := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  have hD := Φ.isEffectiveCartier_boundaryIdeal hΦ hc hN
  obtain ⟨hpre, l, hl, hnumbering⟩ :=
    h.exists_isOrientedCycleSubdivision_boundaryMap (δ := δ) T hΦ hΨ hD hN
  let : PrestableFamily (D[Ψ,hΨ₀] ↘ S) := hpre
  refine ⟨hpre, l, hl, ?_⟩
  intro a'
  obtain ⟨U, hU⟩ := hnumbering a'
  obtain ⟨o', ho'⟩ := h.exists_componentGenericPoint_lift T hΦ hΨ U o
  exact ⟨U, o', hU, ho',
    subdivision_family_of_orientedCycleSubdivision h χ P p hΨ hP U o' hU ho'⟩

/-- A regular fan refinement of a family of marked toric presentations can use
the positive cyclic ray order of the refined fan for its auxiliary numbering.
The common Picard inclusion and the lifted origin present the same marked
fibers, with their original order of internal centers. -/
theorem exists_positive_subdivision_family {C : Type*} (χ : C → Multiplicative (Fin r → ℤ) →* ℂˣ)
    (P : C → MarkedSurface ℂ n B (Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))))
    (p : ∀ t, ContractedToricFiber b s hΦ T o J (χ t) (P t))
    (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
    (hP : ∀ t, ∃ (Y : Scheme) (j : ℕ) (R : BlowupTower (P t).surface j Y)
        (e : Y ≅ (internalBlowupTower b s (centers(χ t))).1),
      IsNodalBoundaryTower Dₘ[P t] ((P t).surface ↘ S) (𝟙 _) R ∧
        (p t).projection = e.inv ≫ R.toBase)
    (u : ZMod m ≃ Φ.Ray)
    (hu : ∀ j, T.component j = Φ.boundaryNormalizationComponentEquiv hΦ (u j))
    (hpos : ∀ j, b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ) :
    ∃ (hpre : PrestableFamily (D[Ψ,hΨ₀] ↘ S)) (l : ℕ) (_ : NeZero l),
      letI := hpre
      ∀ a' : δ → (D[Ψ,hΨ₀] ↘ S).smoothLocus,
        ∃ (U : Scheme.NodalCycleNumbering a' l) (o' : ZMod l) (v : ZMod l ≃ Ψ.Ray),
          (∀ j, U.component j = Ψ.boundaryNormalizationComponentEquiv hΨ (v j)) ∧
          (∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
            ∃ σ : Ψ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ) ∧
          (β).IsOrientedCycleSubdivision U T ∧
          β (U.componentGenericPoint o') = T.componentGenericPoint o ∧
          ∀ t, ∃ (q : ContractedToricFiber b (h.liftRay ∘ s) hΨ U o' J' (χ t) (P t))
            (Y : Scheme) (j : ℕ) (R : BlowupTower (P t).surface j Y)
            (e : Y ≅ (internalBlowupTower b (h.liftRay ∘ s) (centers(χ t))).1),
            IsNodalBoundaryTower Dₘ[P t] ((P t).surface ↘ S) (𝟙 _) R ∧
            q.projection = e.inv ≫ R.toBase ∧ q.boundaryMap = β ≫ (p t).boundaryMap := by
  obtain ⟨hpre, l, hl, hnumbering⟩ :=
    h.exists_positive_boundary_subdivision_numbering b hΦ hΨ hc T u hu hpos (u o)
  let : PrestableFamily (D[Ψ,hΨ₀] ↘ S) := hpre
  refine ⟨hpre, l, hl, fun a' ↦ ?_⟩
  obtain ⟨U, v, hU, -, hv, hpos'⟩ := hnumbering a'
  obtain ⟨o', ho'⟩ := h.exists_componentGenericPoint_lift T hΦ hΨ U o
  exact ⟨U, o', v, hv, hpos', hU, ho',
    subdivision_family_of_orientedCycleSubdivision h χ P p hΨ hP U o' hU ho'⟩

end QPainleve.SignedClusterModularGroup.ContractedToricFiber
