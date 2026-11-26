/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.Numbering
public import QPainleve.Geometry.Toric.Fan.CyclicOrder
public import QPainleve.SignedClusterModularGroup.Realization.ContractionNumerics
public import QPainleve.SignedClusterModularGroup.Realization.Inversion.Contracted
public import QPainleve.SignedClusterModularGroup.Realization.MarkedComparison

import QPainleve.Algebra.Cluster.ChargeKernel.Index

/-!
# Complete marked toric presentations

A complete ordered presentation records the rays bearing the labeled blowup centers,
the positive boundary numbering, and the Picard marking in the auxiliary toric model.
Reversing the lattice frame reverses the boundary numbering and keeps the ordered
centers and Picard inclusion.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Multiplicative Quiver
open Module (Basis)
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric TauCeti.Toric.Fan
open Scheme Scheme.IdealSheafData

namespace QPainleve.SignedClusterModularGroup

open GeometricRealization (Point)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)

variable (i) in
/-- The data common to the fibers of an ordered toric presentation on a complete
regular fan, with positive cyclic numbering and a fixed auxiliary Picard inclusion. -/
structure CompleteToricPresentation (b : Basis (Fin 2) ℤ N) (r : ℕ)
    (L : Type) [AddCommGroup L] (γ : Type*) where
  /-- The complete regular fan of the toric surface. -/
  fan : Fan i
  /-- Completeness of the toric surface fan. -/
  complete : fan.IsComplete
  /-- Regularity of the fan. -/
  regular : fan.IsRegular
  /-- The ray of each internal center, in label order. -/
  rays : Fin r → fan.Ray
  /-- The toric boundary is a prestable curve. -/
  [prestable : PrestableFamily (Dtor[fan,complete.nonempty_cones] ↘ S)]
  /-- The number of components of the toric boundary. -/
  length : ℕ
  /-- The toric boundary has at least one component. -/
  [neZero : NeZero length]
  /-- The marked smooth points used in the boundary numbering. -/
  marks : γ → (Dtor[fan,complete.nonempty_cones] ↘ S).smoothLocus
  /-- The numbering of the components, nodes and branches of the toric boundary. -/
  cycle : Scheme.NodalCycleNumbering marks length
  /-- The ray indexing the first component of the contracted boundary. -/
  origin : ZMod length
  /-- The fixed pullback of the Picard marking in auxiliary toric coordinates. -/
  inclusion : L →ₗ[ℤ] Additive (LineBundleClass fan.algebraicRealization) × (Fin r → ℤ)
  /-- The rays in the order of the toric boundary numbering. -/
  rayOrder : ZMod length ≃ fan.Ray
  /-- The ray order agrees with the numbering of the normalized curve. -/
  component_eq (j : ZMod length) :
    letI := complete.nonempty_cones
    cycle.component j = fan.boundaryNormalizationComponentEquiv regular (rayOrder j)
  /-- Consecutive rays in the positive order span regular two-dimensional cones. -/
  positive (j : ZMod length) :
    b.detDualEquiv (rayOrder j).primitiveGenerator (rayOrder (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : fan.cones, (rayOrder j).toCone ≤ σ ∧ (rayOrder (j + 1)).toCone ≤ σ

variable {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n] {L : Type}
  [AddCommGroup L] {H : LinearMap.BilinForm ℤ L} {γ : Type*}

local notation "A" => (Fin r → ℤ)
local notation "Centers" => Over.mk (structureMap ℂ A)
local notation "XTor" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ(" c ")" => pointsEquiv ℂ A
  (Subtype.mk (CommaMorphism.left (c : Point Centers)) (Over.w (c : Point Centers)))
local notation "centers(" a ")" => fun j : Fin r ↦ (a) (ofAdd (Pi.single j 1))
local notation "Dₘ(" M ")" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))

attribute [local instance] hasUniqueDiv_of_free_int

/-- A contracted fiber whose specified projection is realized by a nodal blowup tower. -/
def CompleteToricPresentation.HasNodalModel (Q : CompleteToricPresentation i b r L γ)
    (c : Point Centers) (M : MarkedSurface ℂ n H XTor) : Prop :=
  letI := Q.complete.nonempty_cones
  letI := Q.prestable
  letI := Q.neZero
  ∃ (p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ(c) M)
    (Y : Scheme) (d : ℕ) (W : BlowupTower M.surface d Y)
    (e : Y ≅ (internalBlowupTower b Q.rays centers(χ(c))).1),
    IsNodalBoundaryTower Dₘ(M) (M.surface ↘ S) (𝟙 _) W ∧ p.projection = e.inv ≫ W.toBase

/-- A nodal model exposes the ordered toric contraction and a nodal tower
whose projection agrees with that contraction. -/
theorem CompleteToricPresentation.hasNodalModel_iff (Q : CompleteToricPresentation i b r L γ)
    (c : Point Centers) (M : MarkedSurface ℂ n H XTor) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    Q.HasNodalModel c M ↔
      ∃ (p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ(c) M)
        (Y : Scheme) (d : ℕ) (W : BlowupTower M.surface d Y)
        (e : Y ≅ (internalBlowupTower b Q.rays centers(χ(c))).1),
        IsNodalBoundaryTower Dₘ(M) (M.surface ↘ S) (𝟙 _) W ∧ p.projection = e.inv ≫ W.toBase :=
  (Iff.rfl)

namespace CompleteToricPresentation

/-- A nodal model supplies the ordered toric contraction in the specified marking. -/
theorem HasNodalModel.nonempty_contractedToricFiber
    {Q : CompleteToricPresentation i b r L γ}
    {c : Point Centers} {M : MarkedSurface ℂ n H XTor} (h : Q.HasNodalModel c M) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    Nonempty (ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ(c) M) := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨p, _⟩ := (Q.hasNodalModel_iff c M).mp h
  exact ⟨p⟩

/-- The ray order of a complete toric presentation is the order induced by
its numbered boundary. -/
theorem rayEquivOfNodalCycleNumbering_eq_rayOrder
    (Q : CompleteToricPresentation i b r L γ) :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    Q.fan.rayEquivOfNodalCycleNumbering Q.regular Q.cycle = Q.rayOrder := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  refine Equiv.ext fun j ↦ (Q.fan.boundaryNormalizationComponentEquiv Q.regular).injective ?_
  rw [Fan.boundaryNormalizationComponentEquiv_rayEquivOfNodalCycleNumbering, Q.component_eq]

/-- The numbered node is the toric fixed point of the cone between its consecutive rays. -/
theorem exists_cone_of_numbered_node (Q : CompleteToricPresentation i b r L γ)
    (j : ZMod Q.length) :
    letI := Q.prestable
    letI := Q.neZero
    ∃ σ : Q.fan.cones, (Q.rayOrder j).toCone ≤ σ ∧
      (Q.rayOrder (j + 1)).toCone ≤ σ ∧
      (Q.fan.boundaryIdeal Q.complete.nonempty_cones).subschemeι
        ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme.dualGraphEdgeEquiv
          Q.marks (Q.cycle.edge j)).val =
        Q.fan.distinguishedPointHom σ (IsLocalRing.closedPoint ℂ) := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨_, -, _, hnodes⟩ :=
    Q.fan.exists_positive_ray_numbering_of_nodalCycleNumbering b Q.regular Q.complete Q.cycle
  rw [Q.rayEquivOfNodalCycleNumbering_eq_rayOrder] at hnodes
  obtain ⟨σ, h₀, h₁, hpoint⟩ := hnodes j
  exact ⟨σ.val, h₀, h₁, hpoint⟩

/-- A nodal contraction of a marked toric fiber supplies a nodal model at its center. -/
theorem hasNodalModel_of_contraction (Q : CompleteToricPresentation i b r L γ)
    {c : Point Centers} {M : MarkedSurface ℂ n H XTor} :
    letI := Q.complete.nonempty_cones
    letI := Q.prestable
    letI := Q.neZero
    ∀ {p : ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ(c) M},
      p.IsNodalContraction → Q.HasNodalModel c M := by
  intro p hp
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨l, Y, W, hW, e, he⟩ := hp.exists_tower
  exact (Q.hasNodalModel_iff c M).mpr ⟨p, Y, l, W, e, hW, he.symm⟩

/-- A charge seed realizing the determinant pairing and rays of a presentation has a
nonzero exchange matrix when the ray charges span a finite-index sublattice. -/
theorem exchangeMatrix_ne_zero_of_chargeIndex_ne_zero
    (Q : CompleteToricPresentation i b r L γ) {E : SkewExchangeMatrix (Fin r)}
    (P : ChargeSeed E N)
    (hform : P.form = b.detDualEquiv.toLinearMap) (hcharge : P.charge = Fan.rayChargeMap Q.rays)
    (hindex : (Fan.rayChargeMap Q.rays).range.toAddSubgroup.index ≠ 0) :
    E.matrix ≠ 0 := by
  rw [← P.matrix_eq, hform, hcharge]
  exact ((Fan.rayChargeMap Q.rays).chargeExchangeMatrix_eq_zero_iff_index_range_eq_zero b
    b.detDualEquiv_self b.detDualEquiv_apply_basis_zero_one).not.mpr hindex

/-- The inclusion in the auxiliary Picard lattice is injective whenever the
presentation has a nodal model. -/
theorem inclusion_injective (Q : CompleteToricPresentation i b r L γ)
    {c : Point Centers} {M : MarkedSurface ℂ n H XTor} (h : Q.HasNodalModel c M) :
    Function.Injective Q.inclusion := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨p, _, _, W, e, hW, hp⟩ := (Q.hasNodalModel_iff c M).mp h
  let : IsIntegral M.surface := M.integral
  let : M.surface.IsProjectiveOver ℂ := M.projective
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : Smooth (M.surface ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
  intro x y hxy
  rw [← p.marked_pullback x, ← p.marked_pullback y] at hxy
  apply M.picardMarking.injective
  apply Additive.toMul.injective
  apply hW.isClosedPointTower.injective_pullback_toBase (M.surface ↘ S)
  apply (LineBundleClass.pullbackEquiv e.symm).injective
  have h := Additive.ofMul.injective
    ((Fan.internalBlowupPicardMarking b Q.rays centers(χ(c)) Q.regular).symm.injective hxy)
  simpa only [hp, LineBundleClass.pullback_comp, LineBundleClass.pullbackEquiv_apply,
    Iso.symm_hom] using h

/-- Read the same ordered toric presentation in the reversed lattice frame.
The numbered boundary is read from the same geometric origin in reverse order. -/
-- The fan and the length reduce in the types of dependent projections of the reverse.
@[expose]
def invert (Q : CompleteToricPresentation i b r L γ) :
    CompleteToricPresentation i (b.reindex (Equiv.swap 0 1)) r L γ := by
  letI := Q.prestable
  letI := Q.neZero
  exact
    { fan := Q.fan
      complete := Q.complete
      regular := Q.regular
      rays := Q.rays
      prestable := Q.prestable
      length := Q.length
      neZero := Q.neZero
      marks := Q.marks
      cycle := Q.cycle.reverse
      origin := -Q.origin
      inclusion := Q.inclusion
      rayOrder := (Equiv.neg _).trans Q.rayOrder
      component_eq j := by
        rw [NodalCycleNumbering.reverse_component]
        exact Q.component_eq (-j)
      positive j := cyclicRayNumbering_neg b Q.rayOrder Q.positive j }

/-- The ordered centers lie on the same rays in the reversed frame. -/
@[simp]
theorem invert_rays (Q : CompleteToricPresentation i b r L γ) : Q.invert.rays = Q.rays := (rfl)

/-- The origin retains its geometric component under the reversed numbering. -/
@[simp]
theorem invert_origin (Q : CompleteToricPresentation i b r L γ) :
    Q.invert.origin = -Q.origin := (rfl)

/-- The reversal of the numbered rays acts by negation on component numbers. -/
@[simp]
theorem invert_rayOrder (Q : CompleteToricPresentation i b r L γ) (j : ZMod Q.length) :
    Q.invert.rayOrder j = Q.rayOrder (-j) := (rfl)

/-- At the image of a center under inversion, the reversed presentation uses the
original nodal tower and the reversed marked pair. -/
theorem hasNodalModel_invert (Q : CompleteToricPresentation i b r L γ)
    (E : Cluster.SkewExchangeMatrix (Fin r))
    (M : Point Centers → MarkedSurface ℂ n H XTor) (y : Point Centers)
    (h : Q.HasNodalModel
      (y ≫ ((Cluster.Generator.invert.toStep E).toPath.centerIsoOver ℂ).inv)
      (M (y ≫ ((Cluster.Generator.invert.toStep E).toPath.centerIsoOver ℂ).inv))) :
    Q.invert.HasNodalModel y
      ((M (y ≫ ((Cluster.Generator.invert.toStep E).toPath.centerIsoOver ℂ).inv)).invert) := by
  let := Q.complete.nonempty_cones
  let := Q.prestable
  let := Q.neZero
  obtain ⟨p, Y, d, W, e, hW, hp⟩ := (Q.hasNodalModel_iff _ _).mp h
  obtain ⟨q, e', hW', hq, -⟩ := GeometricRealization.exists_invert_contracted E M y p W e hW hp
  exact (Q.invert.hasNodalModel_iff _ _).mpr ⟨q, Y, d, W, e', hW', hq⟩

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
