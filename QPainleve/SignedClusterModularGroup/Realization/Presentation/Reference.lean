/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Presentation.Basic
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Surface.Boundary

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Subdivision
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.Geometry.Toric.Fan.Boundary.Numbering
import QPainleve.Geometry.Toric.Fan.Boundary.Prestable
import QPainleve.Geometry.Toric.Fan.CyclicOrder
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Reference fibers of complete toric presentations

A toric presentation of a numbered nodal pair supplies a marked reference fiber.
The orientation on the original boundary determines the orientation on the fan.
The reference marking pulls back along the given nodal contraction to the ordered
Picard coordinates of the internal blowups. This fixes the lattice inclusion and
the boundary origin used when the centers vary.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative TopologicalSpace QPainleve.BlowupTower
open QPainleve.CharacterTorus TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

local notation "S" => Spec (CommRingCat.of ℂ)

local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "param[" c "]" => (fun j ↦ χ[c] (ofAdd (Pi.single j 1)))

/-- A reference fiber on the original surface of a numbered nodal pair.
The chosen toric presentation and center give a nodal model with the supplied
Picard marking and the recorded rational X evaluation. -/
@[ext]
structure MarkedReferenceFiber {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
    (i : N →+ V) (b : Module.Basis (Fin 2) ℤ N) (r : ℕ)
    {X : Scheme} [X.Over S] [IsIntegral X] [X.IsProjectiveOver ℂ]
    [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData}
    [PrestableFamily (D.subscheme ↘ S)] {n : ℕ} [NeZero n]
    {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (μ : B.IsometryEquiv (Chow.intersectionBilinForm ℂ X)) where
  /-- The complete presentation in the frame `b`. -/
  presentation : CompleteToricPresentation i b r L Empty
  /-- The point of the center torus representing the original pair. -/
  center : GeometricRealization.Point Centers[r]
  /-- The rational X evaluation on the original surface. -/
  evaluation : X ⤏ XTor[r]
  /-- The reference surface with this evaluation has the indicated nodal model. -/
  hasNodalModel : presentation.HasNodalModel center (MarkedSurface.ofBoundary D A μ evaluation)

section Reference

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {X W : Scheme} [X.Over S] [IsIntegral X] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ S)] {n r k : ℕ} [NeZero n]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {Φ : Fan i} [h₀ : Nonempty Φ.cones] {b : Module.Basis (Fin 2) ℤ N} {T : BlowupTower X k W}
  (A : Scheme.NodalCycleNumbering (X := D.subscheme)
    (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
  (μ : B.IsometryEquiv (Chow.intersectionBilinForm ℂ X))
  (hΦ : Φ.IsRegular) (s : Fin r → Φ.Ray)
  (c : GeometricRealization.Point Centers[r])

local notation "TorBoundary" => IdealSheafData.subscheme (Φ.boundaryIdeal h₀)
local notation "U" => Fan.internalBlowupTower b s param[c]

private theorem exists_boundary_subdivision (hD : D.IsEffectiveCartier)
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : U.1 ≅ W) (hbase : e.hom ≫ T.toBase ≫ (X ↘ S) =
      U.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
    (hker : ((D.comap T.toBase).radical).comap e.hom = U.2.boundaryι.ker)
    [PrestableFamily (TorBoundary ↘ S)] :
    letI : NeZero (n + k) := ⟨by have := NeZero.ne n; omega⟩
    ∃ (C : Scheme.NodalCycleNumbering (X := TorBoundary)
        (Empty.elim : Empty → (TorBoundary ↘ S).smoothLocus) (n + k))
      (g : TorBoundary ⟶ D.subscheme),
      g ≫ D.subschemeι = U.2.boundaryι ≫ e.hom ≫ T.toBase ∧
      g.IsOver S ∧ g.IsOrientedCycleSubdivision C A := by
  let π := e.hom ≫ T.toBase
  let E := (D.comap π).radical
  let : U.1.Over S := ⟨U.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap⟩
  have hπ : π.IsOver S := ⟨(Category.assoc _ _ _).trans hbase⟩
  have hE : E = U.2.boundaryι.ker := by
    dsimp only [E, π]
    rw [← hker, comap_comp, radical_comap_of_isOpenImmersion (D.comap T.toBase) e.hom]
  obtain ⟨a, ha⟩ := E.exists_iso_of_comap_eq_ker (Iso.refl _) U.2.boundaryι
    (by simpa only [Iso.refl_hom, comap_id] using hE)
  rw [Iso.refl_hom, Category.comp_id] at ha
  let : a.hom.IsOver S := ⟨by
    rw [E.over_eq_subschemeι_comp, ← Category.assoc, ha]
    exact ((U.2.boundaryι_toBase_assoc _).trans
      ((Φ.boundaryIdeal h₀).over_eq_subschemeι_comp.trans
        (by rw [Φ.algebraicRealization_over])).symm)⟩
  obtain ⟨hpre, hnumber⟩ :=
    hT.exists_isOrientedCycleSubdivision_nodalBoundaryTower_of_iso hD A e rfl hπ
  let := hpre
  let : NeZero (n + k) := ⟨by have := NeZero.ne n; omega⟩
  obtain ⟨C, hβ, hsub⟩ := hnumber (Empty.elim : Empty → (E.subscheme ↘ S).smoothLocus)
  let β := E.subschemeMap D π (le_map_iff_comap_le.mpr (le_radical _))
  let : β.IsOver S := hβ
  let : a.symm.hom.IsOver S := inferInstanceAs (a.inv.IsOver S)
  let C' := a.symm.mapNodalCycleNumbering C
    (q := (Empty.elim : Empty → (TorBoundary ↘ S).smoothLocus))
  have hact : a.boundaryCycleAction C' C = 1 := by
    have h := a.symm.boundaryCycleAction_symm C C'
    rw [a.symm.boundaryCycleAction_mapNodalCycleNumbering C, inv_one] at h
    exact h
  have hsign : DihedralGroup.cycleOrientationSign (a.boundaryCycleAction C' C) = 1 := by
    rw [hact, map_one]
  refine ⟨C', a.hom ≫ β, ?_, inferInstance,
    (a.isOrientedCycleSubdivision_of_cycleOrientationSign_eq_one C' C hsign).comp hsub⟩
  rw [Category.assoc, subschemeMap_subschemeι, ← Category.assoc, ha]

private theorem exists_positive_boundary_subdivision (hD : D.IsEffectiveCartier)
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : U.1 ≅ W) (hbase : e.hom ≫ T.toBase ≫ (X ↘ S) =
      U.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
    (hker : ((D.comap T.toBase).radical).comap e.hom = U.2.boundaryι.ker)
    (hc : Φ.IsComplete) [PrestableFamily (TorBoundary ↘ S)] [NeZero (n + k)] :
    ∃ (C : Scheme.NodalCycleNumbering (X := TorBoundary)
        (Empty.elim : Empty → (TorBoundary ↘ S).smoothLocus) (n + k))
      (g : TorBoundary ⟶ D.subscheme) (a : Module.Basis (Fin 2) ℤ N),
      g ≫ D.subschemeι = U.2.boundaryι ≫ e.hom ≫ T.toBase ∧
        g.IsOver S ∧ g.IsOrientedCycleSubdivision C A ∧
        (a = b ∨ a = b.reindex (Equiv.swap 0 1)) ∧
        ∀ j, let v := Φ.rayEquivOfNodalCycleNumbering hΦ C
          a.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
            ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ := by
  obtain ⟨C, g, hg, hgOver, hsub⟩ := exists_boundary_subdivision A s c hD hT e hbase hker
  obtain ⟨a, ha, hpos, hnodes⟩ := Φ.exists_positive_ray_numbering_of_nodalCycleNumbering b hΦ hc C
  refine ⟨C, g, a, hg, hgOver, hsub, ha, fun j ↦ ?_⟩
  obtain ⟨σ, h₀, h₁, _⟩ := hnodes j
  exact ⟨hpos j, σ.val, h₀, h₁⟩

omit [IsIntegral X] [X.IsProjectiveOver ℂ] [SmoothOfRelativeDimension 2 (X ↘ S)] in
private theorem exists_boundary_origin [PrestableFamily (TorBoundary ↘ S)] [NeZero (n + k)]
    (C : Scheme.NodalCycleNumbering (X := TorBoundary)
      (Empty.elim : Empty → (TorBoundary ↘ S).smoothLocus) (n + k))
    {π : U.1 ⟶ X} [Surjective π] (g : TorBoundary ⟶ D.subscheme)
    (hsupp : (D.comap π).support = U.2.boundaryι.ker.support)
    (hg : g ≫ D.subschemeι = U.2.boundaryι ≫ π) :
    ∃ o, g (C.componentGenericPoint o) = A.componentGenericPoint 0 := by
  have : Surjective g := ⟨fun y ↦ by
    obtain ⟨x, hx⟩ := π.surjective (D.subschemeι y)
    have hmem : x ∈ (D.comap π).support := by
      rw [← SetLike.mem_coe, support_comap, Closeds.coe_preimage, Set.mem_preimage, hx,
        ← D.range_subschemeι]
      exact Set.mem_range_self y
    rw [hsupp, ← SetLike.mem_coe, Scheme.Hom.support_ker,
      U.2.boundaryι.isClosedMap.isClosed_range.closure_eq] at hmem
    obtain ⟨z, rfl⟩ := hmem
    refine ⟨z, D.subschemeι.isClosedEmbedding.injective ?_⟩
    rwa [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]⟩
  exact A.exists_componentGenericPoint_over C g 0

private theorem exists_reference_of_numbered_model
    (hc : Φ.IsComplete) (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : U.1 ≅ W) (hbase : e.hom ≫ T.toBase ≫ (X ↘ S) =
      U.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
    (hker : ((D.comap T.toBase).radical).comap e.hom = U.2.boundaryι.ker)
    [PrestableFamily (TorBoundary ↘ S)] [NeZero (n + k)]
    (C : Scheme.NodalCycleNumbering (X := TorBoundary)
      (Empty.elim : Empty → (TorBoundary ↘ S).smoothLocus) (n + k))
    (g : TorBoundary ⟶ D.subscheme) [g.IsOver S]
    (hg : g ≫ D.subschemeι = U.2.boundaryι ≫ e.hom ≫ T.toBase)
    (hsub : g.IsOrientedCycleSubdivision C A)
    (hpos : ∀ j, let u := Φ.rayEquivOfNodalCycleNumbering hΦ C
      b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
        ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ) :
    ∃ R : MarkedReferenceFiber i b r A μ,
      R.center = c ∧ ∃ hfan : R.presentation.fan = Φ, hfan ▸ R.presentation.rays = s := by
  let π := e.hom ≫ T.toBase
  have : IsModification T.toBase :=
    hT.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  have hπ : IsModification π := inferInstanceAs (IsModification (e.hom ≫ T.toBase))
  let := hπ
  have hsupp : (D.comap π).support = U.2.boundaryι.ker.support := by
    rw [← hker, ← radical_comap_of_isOpenImmersion _ e.hom, ← comap_comp, support_radical]
  obtain ⟨o, ho⟩ := exists_boundary_origin A s c C g hsupp
    (hg.trans (Category.assoc _ _ _).symm)
  -- The reference inclusion is the actual pullback in the ordered blowup coordinates.
  let ι := (Fan.internalBlowupPicardMarking b s param[c] hΦ).symm.toLinearMap.comp
    (((LineBundleClass.pullbackHom π).toAdditive.toIntLinearMap).comp μ.toLinearEquiv.toLinearMap)
  let Q : CompleteToricPresentation i b r L Empty := {
    fan := Φ, complete := hc, regular := hΦ, rays := s
    prestable := inferInstance
    length := n + k
    neZero := inferInstance
    marks := Empty.elim
    cycle := C
    origin := o
    inclusion := ι
    rayOrder := Φ.rayEquivOfNodalCycleNumbering hΦ C
    component_eq := fun j ↦
      (Fan.boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering hΦ C j).symm
    positive := hpos }
  let f := Fan.contractedXEvaluation b s χ[c] hΦ π
  let M := MarkedSurface.ofBoundary D A μ f
  let p : ContractedToricFiber b s hΦ C o ι χ[c] M := {
    projection := π
    modification := hπ
    projection_over := (Category.assoc _ _ _).trans hbase
    support_comap := by
      dsimp only [M]
      rw [MarkedSurface.ofBoundary_ker]
      exact hsupp
    boundaryMap := g
    boundary_comp := hg
    boundary_over := inferInstanceAs (g.IsOver S)
    orientedSubdivision := hsub
    component_zero := ho
    marked_pullback := fun x ↦ by
      dsimp only [M]
      rw [MarkedSurface.ofBoundary_picardMarking]
      simp [ι]
      rfl
    evaluation_eq := MarkedSurface.ofBoundary_evaluation .. }
  have hmodel : Q.HasNodalModel c M := (Q.hasNodalModel_iff c M).mpr
    ⟨p, W, k, T, e.symm, by
      dsimp only [M]
      rwa [MarkedSurface.ofBoundary_ker], rfl⟩
  exact ⟨⟨Q, c, f, hmodel⟩, rfl, rfl, rfl⟩

private theorem exists_reference_with_swapped_basis
    (hc : Φ.IsComplete) (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : U.1 ≅ W) (hbase : e.hom ≫ T.toBase ≫ (X ↘ S) =
      U.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap)
    (hker : ((D.comap T.toBase).radical).comap e.hom = U.2.boundaryι.ker)
    [PrestableFamily (TorBoundary ↘ S)] [NeZero (n + k)]
    (C : Scheme.NodalCycleNumbering (X := TorBoundary)
      (Empty.elim : Empty → (TorBoundary ↘ S).smoothLocus) (n + k))
    (g : TorBoundary ⟶ D.subscheme) [g.IsOver S]
    (hg : g ≫ D.subschemeι = U.2.boundaryι ≫ e.hom ≫ T.toBase)
    (hsub : g.IsOrientedCycleSubdivision C A)
    (hpositive : ∀ j, let v := Φ.rayEquivOfNodalCycleNumbering hΦ C
      (b.reindex (Equiv.swap 0 1)).detDualEquiv (v j).primitiveGenerator
        (v (j + 1)).primitiveGenerator = 1 ∧
          ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ) :
    ∃ R : MarkedReferenceFiber i (b.reindex (Equiv.swap 0 1)) r A μ,
      param[R.center] = param[c]⁻¹ ∧
        (∃ hfan : R.presentation.fan = Φ, hfan ▸ R.presentation.rays = s) := by
  let c' := centerPoint param[c]⁻¹
  have hc' := centerPoint_parameters param[c]⁻¹
  let U' := Fan.internalBlowupTower (b.reindex (Equiv.swap 0 1)) s param[c']
  -- The frame change preserves the two maps from the ordered blowup model.
  have hcompare : ∃ v : U'.1 ≅ U.1, v.hom ≫ U.2.toTower.toBase = U'.2.toTower.toBase ∧
      U'.2.boundaryι ≫ v.hom = U.2.boundaryι := by
    dsimp only [U']
    rw [hc']
    let w := eqToIso (congrArg Sigma.fst (Fan.internalBlowupTower_reindex_swap b s param[c]).symm)
    obtain ⟨hproj, hboundary, _⟩ := Fan.internalBlowupTower_reindex_swap_iso b s param[c] hΦ
    refine ⟨w.symm, ?_, ?_⟩
    · rw [Iso.symm_hom, ← hproj, Iso.inv_hom_id_assoc]
    · rw [Iso.symm_hom, ← hboundary, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  obtain ⟨v, hproj, hboundary⟩ := hcompare
  have hb' : (v ≪≫ e).hom ≫ T.toBase ≫ (X ↘ S) =
      U'.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap := by
    simp only [Iso.trans_hom, Category.assoc, hbase]
    exact (reassoc_of% hproj) _
  have hker' : ((D.comap T.toBase).radical).comap (v ≪≫ e).hom = U'.2.boundaryι.ker := by
    rw [Iso.trans_hom, comap_comp, hker, ← hboundary,
      Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  have hg' : g ≫ D.subschemeι = U'.2.boundaryι ≫ (v ≪≫ e).hom ≫ T.toBase := by
    simp only [Iso.trans_hom, Category.assoc]
    exact hg.trans ((reassoc_of% hboundary) _).symm
  obtain ⟨R, hcenter, hrays⟩ :=
    exists_reference_of_numbered_model A μ hΦ s c' hc hT (v ≪≫ e) hb' hker'
      C g hg' hsub hpositive
  exact ⟨R, hcenter ▸ hc', hrays⟩

end Reference

section FromToricPresentation

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {X : Scheme} [X.Over S] [IsIntegral X] [X.IsProjectiveOver ℂ]
  [SmoothOfRelativeDimension 2 (X ↘ S)] {D : X.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ S)] {n : ℕ} [NeZero n]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {b : Module.Basis (Fin 2) ℤ N}

section OrderedTowers

variable {Φ : Fan i} (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    {r k : ℕ} (s : Fin r → Φ.Ray) (u : Fin r → ℂˣ)
    {W : Scheme} {T : BlowupTower X k W}
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (e : (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).1 ≅ W)
    (hbase : e.hom ≫ T.toBase ≫ (X ↘ S) =
      (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).2.toTower.toBase ≫
        Φ.algebraicRealizationStructureMap)
    (hker : ((D.comap T.toBase).radical).comap e.hom =
      (Fan.internalBlowupTower (h₀ := hc.nonempty_cones) b s u).2.boundaryι.ker)
    (hD : D.IsEffectiveCartier)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (μ : B.IsometryEquiv (Chow.intersectionBilinForm ℂ X))

include hΦ hc hT e hbase hker hD

private theorem exists_marked_reference_fibers :
    (∃ (b' : Module.Basis (Fin 2) ℤ N) (R : MarkedReferenceFiber i b' r A μ),
      ((b' = b ∧ param[R.center] = u) ∨
        (b' = b.reindex (Equiv.swap 0 1) ∧ param[R.center] = u⁻¹)) ∧
        (∃ hfan : R.presentation.fan = Φ, hfan ▸ R.presentation.rays = s)) ∧
    (∃ (A' : Scheme.NodalCycleNumbering (X := D.subscheme)
        (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
      (R : MarkedReferenceFiber i b r A' μ),
      (A' = A ∨ A' = A.reverse) ∧ param[R.center] = u ∧
        (∃ hfan : R.presentation.fan = Φ, hfan ▸ R.presentation.rays = s)) := by
  let := hc.nonempty_cones
  have hdim : Module.finrank ℤ N = 2 := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : IsProper Φ.algebraicRealizationStructureMap := by
    have := Φ.isProjectiveOver_algebraicRealization_of_isComplete hΦ hc b
    rw [← Φ.algebraicRealization_over]
    infer_instance
  let := Φ.prestableFamily_boundary hΦ hc hdim
  obtain ⟨c, hcparam⟩ : ∃ c : GeometricRealization.Point Centers[r], param[c] = u :=
    ⟨centerPoint u, centerPoint_parameters u⟩
  subst u
  let : NeZero (n + k) := ⟨by have := NeZero.ne n; omega⟩
  obtain ⟨C, g, a, hg, hgOver, hsub, ha, hpositive⟩ :=
    exists_positive_boundary_subdivision A hΦ s c hD hT e hbase hker hc
  let := hgOver
  rcases ha with ha | ha
  · subst a
    obtain ⟨R, hcenter, hrays⟩ :=
      exists_reference_of_numbered_model A μ hΦ s c hc hT e hbase hker C g hg hsub hpositive
    refine ⟨⟨b, R, Or.inl ⟨rfl, ?_⟩, hrays⟩, ⟨A, R, Or.inl rfl, ?_, hrays⟩⟩ <;>
      rw [hcenter]
  · subst a
    have hray (j : ZMod (n + k)) :
        Φ.rayEquivOfNodalCycleNumbering hΦ C.reverse j =
          Φ.rayEquivOfNodalCycleNumbering hΦ C (-j) := by
      apply (Φ.boundaryNormalizationComponentEquiv hΦ).injective
      simp only [Fan.boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering,
        NodalCycleNumbering.reverse_component]
    have hswap : (b.reindex (Equiv.swap 0 1)).reindex (Equiv.swap 0 1) = b := by
      apply DFunLike.ext
      intro j
      simp only [Module.Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_self]
    have hpositive' (j : ZMod (n + k)) :
        let u := Φ.rayEquivOfNodalCycleNumbering hΦ C.reverse
        b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
          ∃ σ : Φ.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ := by
      simpa only [hray, hswap] using
        Fan.cyclicRayNumbering_neg (b.reindex (Equiv.swap 0 1)) _ hpositive j
    obtain ⟨R, hparam, hrays⟩ :=
      exists_reference_with_swapped_basis A μ hΦ s c hc hT e hbase hker C g hg hsub hpositive
    obtain ⟨R', hcenter', hrays'⟩ :=
      exists_reference_of_numbered_model A.reverse μ hΦ s c hc hT e hbase hker
        C.reverse g hg hsub.reverse hpositive'
    exact ⟨⟨_, R, Or.inr ⟨rfl, hparam⟩, hrays⟩,
      ⟨_, R', Or.inr rfl, by rw [hcenter'], hrays'⟩⟩

/-- Equip specified ordered toric and nodal blowup towers with a complete marking
and use their common surface to obtain the reference fiber. The fan and the ray of
each label are retained. If the boundary orientation calls for the transposed
basis, every center parameter is inverted in that basis. -/
theorem exists_marked_reference_fiber_of_ordered_towers :
    ∃ (b' : Module.Basis (Fin 2) ℤ N) (R : MarkedReferenceFiber i b' r A μ),
      ((b' = b ∧ param[R.center] = u) ∨
        (b' = b.reindex (Equiv.swap 0 1) ∧ param[R.center] = u⁻¹)) ∧
        (∃ hfan : R.presentation.fan = Φ, hfan ▸ R.presentation.rays = s) :=
  (exists_marked_reference_fibers hΦ hc s u hT e hbase hker hD A μ).1

/-- Mark the specified ordered toric and nodal towers in the original lattice basis.
The boundary numbering downstairs is chosen from the supplied numbering and its
reverse, so that the fan has positive cyclic order in that basis. -/
theorem exists_marked_reference_fiber_of_ordered_towers_fixed_basis :
    ∃ (A' : Scheme.NodalCycleNumbering (X := D.subscheme)
        (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
      (R : MarkedReferenceFiber i b r A' μ),
      (A' = A ∨ A' = A.reverse) ∧ param[R.center] = u ∧
        (∃ hfan : R.presentation.fan = Φ, hfan ▸ R.presentation.rays = s) :=
  (exists_marked_reference_fibers hΦ hc s u hT e hbase hker hD A μ).2

end OrderedTowers

/-- A toric presentation of a numbered Cartier boundary gives a complete marked
presentation with a reference fiber on the same surface. The given numbering and
Picard marking are retained. The construction permits repeated internal centers
and their corresponding infinitely near blowups. -/
theorem exists_marked_reference_fiber_of_toric_presentation
    (hP : D.HasToricPresentation (X ↘ S) b i) (hD : D.IsEffectiveCartier)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n)
    (μ : B.IsometryEquiv (Chow.intersectionBilinForm ℂ X)) :
    ∃ (b' : Module.Basis (Fin 2) ℤ N) (r : ℕ) (_ : MarkedReferenceFiber i b' r A μ),
      b' = b ∨ b' = b.reindex (Equiv.swap 0 1) := by
  obtain ⟨r, ⟨P⟩⟩ := (hasToricPresentation_iff ..).mp hP
  obtain ⟨b', R, hframe, _⟩ :=
    exists_marked_reference_fiber_of_ordered_towers P.regular P.complete P.rays P.parameters
      P.isNodal P.iso P.iso_over P.iso_boundary hD A μ
  exact ⟨b', r, R, hframe.imp And.left And.left⟩

/-- A specified toric presentation on a surface with finite free Picard group admits a
reference fiber marked by a finite coordinate lattice. The fan and ray labels are retained.
The reference center parameters are inverted if the lattice basis is transposed. -/
theorem exists_fin_marked_reference_fiber_of_toric_presentation {r : ℕ}
    [Module.Free ℤ (Additive (LineBundleClass X))] [Module.Finite ℤ (Additive (LineBundleClass X))]
    (P : D.ToricPresentation (X ↘ S) b i r) (hD : D.IsEffectiveCartier)
    (A : Scheme.NodalCycleNumbering (X := D.subscheme)
      (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus) n) :
    ∃ (H : LinearMap.BilinForm ℤ (Fin (Module.finrank ℤ (Additive (LineBundleClass X))) → ℤ))
      (μ : H.IsometryEquiv (Chow.intersectionBilinForm ℂ X))
      (b' : Module.Basis (Fin 2) ℤ N) (R : MarkedReferenceFiber i b' r A μ),
      ((b' = b ∧ param[R.center] = P.parameters) ∨
        (b' = b.reindex (Equiv.swap 0 1) ∧ param[R.center] = P.parameters⁻¹)) ∧
        (∃ hfan : R.presentation.fan = P.fan, hfan ▸ R.presentation.rays = P.rays) := by
  let a := (Module.finBasis ℤ (Additive (LineBundleClass X))).equivFun.symm
  let μ := ((Chow.intersectionBilinForm ℂ X).isometryEquivOfCompLinearEquiv a).symm
  obtain ⟨b', R, hframe, hrays⟩ :=
    exists_marked_reference_fiber_of_ordered_towers P.regular P.complete P.rays P.parameters
      P.isNodal P.iso P.iso_over P.iso_boundary hD A μ
  exact ⟨_, μ, b', R, hframe, hrays⟩

end FromToricPresentation

end QPainleve.SignedClusterModularGroup
