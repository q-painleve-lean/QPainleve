/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.AffineA1
public import QPainleve.SignedClusterModularGroup.Examples.FourVertex.Generation

import QPainleve.Data.Fin.Find
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Faithfulness

/-!
# Integer comparison for the four-vertex Picard action

The exchange-kernel basis corresponds to the two alternating Picard classes.
In these coordinates, the sign, the signed orthogonal restriction and the forward
boundary index determine a Picard isometry. Comparing these data with the integer
invariants of the three cluster words identifies the corresponding pullbacks in the
explicit octagon lattice. The boundary label used in the comparison is the index
of the class pulled back to component zero. This transfers the lattice generation
theorems to a faithful Picard action of the independent X maps.

The comparison uses `Quiver.Path.signedLoopInvariants` and
`signed_boundary_isometry_eq_iff`.
-/

public noncomputable section

open CategoryTheory Module MulOpposite Quiver
open scoped Matrix

namespace QPainleve.FourVertex

open Cluster SignedBoundaryIsometryGroup

local notation "B" => exchangeMatrix
local notation "K" => intersectionForm.orthogonal (Submodule.span ℤ (Set.range boundaryClass))
local notation "E" => exchangeMatrix.matrix.mulVecLin.ker
local notation "G" => signedBoundaryIsometryGroup intersectionForm boundaryClass
local notation "ι" => rotationInclusion intersectionForm boundaryClass
local notation "η" => sign intersectionForm boundaryClass
local notation "res" => signedOrthogonalRestriction intersectionForm boundaryClass
local notation "picard" => toIsometry intersectionForm boundaryClass
local notation "label" => ZMod.finEquiv 8
local notation "trop[" w "]" =>
  Equiv.toFun (CategoryTheory.Functor.map (Paths.lift (tropicalPrefunctor (A := ℤ) (Fin 4))) w)

local notation "e" => boundaryOrthogonalEquivExchangeKernel

/-- Read a signed octagon isometry in the same integer coordinates as a loop.
The columns are the signed restrictions of the two basis vectors, written in the
ambient exponent lattice. The last entry is the forward image of component zero. -/
def picardInvariants (g : G) : SignedLoopInvariants (Fin 4) (Fin 2) 8 where
  sign := η g
  kernelColumns :=
    Matrix.of (fun i j ↦ (e ((res g).val (boundaryOrthogonalBasis j)) : Fin 4 → ℤ) i)
  boundaryLabel :=
    Fin.find? fun j ↦ decide ((picard g).val (boundaryClass (label j)) = boundaryClass 0)

/-- The first invariant of a signed Picard isometry is its sign. -/
@[simp]
theorem picardInvariants_sign (g : G) : (picardInvariants g).sign = η g :=
  (rfl)

/-- Each column records the signed image of the corresponding orthogonal basis class. -/
@[simp]
theorem picardInvariants_kernelColumns_apply (g : G) (i : Fin 4) (j : Fin 2) :
    (picardInvariants g).kernelColumns i j =
      (e ((res g).val (boundaryOrthogonalBasis j)) : Fin 4 → ℤ) i :=
  (rfl)

private theorem boundaryClass_injective : Function.Injective boundaryClass := by decide

/-- A successful search returns precisely the component whose class pulls back to component zero. -/
@[simp]
theorem picardInvariants_label_eq_some_iff (g : G) (j : Fin 8) :
    (picardInvariants g).boundaryLabel = some j ↔
      (picard g).val (boundaryClass (label j)) = boundaryClass 0 := by
  exact Fin.find?_decide_eq_some_iff_of_injective
    (f := fun k ↦ (picard g).val (boundaryClass (label k)))
    ((picard g).val.injective.comp (boundaryClass_injective.comp (label).injective)) _ j

/-- Every signed octagon isometry has a forward boundary label. -/
theorem exists_picardInvariants_label (g : G) :
    ∃ j : Fin 8, (picardInvariants g).boundaryLabel = some j := by
  obtain ⟨a, _, ha⟩ := exists_cycleAction_pullback intersectionForm boundaryClass g
  exact ⟨(label).symm (DihedralGroup.cycleVertexPerm a 0),
    (picardInvariants_label_eq_some_iff _ _).mpr (by
      simpa only [RingEquiv.apply_symm_apply] using ha 0)⟩

/-- The sign, exponent columns and forward boundary label determine the signed
octagon isometry on its entire Picard lattice. -/
theorem picardInvariants_injective : Function.Injective picardInvariants := by
  intro g h heq
  have hη : η g = η h := by
    simpa only [picardInvariants_sign] using congrArg SignedLoopInvariants.sign heq
  have hres : (res g).val = (res h).val := by
    apply LinearEquiv.toLinearMap_injective
    apply boundaryOrthogonalBasis.ext
    intro j
    apply (e).injective
    apply Subtype.ext
    funext i
    simpa only [picardInvariants_kernelColumns_apply, LinearEquiv.coe_coe] using
      congrArg (fun data : SignedLoopInvariants (Fin 4) (Fin 2) 8 ↦ data.kernelColumns i j) heq
  obtain ⟨j, hj⟩ := exists_picardInvariants_label g
  have hj' : (picardInvariants h).boundaryLabel = some j :=
    (congrArg SignedLoopInvariants.boundaryLabel heq).symm.trans hj
  have hforward (a : G) (ha : (picardInvariants a).boundaryLabel = some j) :
      ∀ i, (picard a).val (boundaryClass i) = boundaryClass (η a • (i - label j)) := by
    apply (boundary_pullback_eq_smul_sub_iff boundaryClass_injective ?_).mpr
      ((picardInvariants_label_eq_some_iff _ _).mp ha)
    simpa only [toIsometry_apply, sign_apply] using
      (mem_signedBoundaryIsometryGroup_iff _ _).mp a.property
  let iso := intersectionForm.isometryGroupEquivIsometryEquiv
  have he := signed_boundary_isometry_eq_iff
    (g := iso (picard g)) (h := iso (picard h)) (j := label j) (j' := label j)
    intersectionForm_isSymm intersectionForm_nondegenerate.1
    (BoundaryCycle.span_sup_orthogonal_rat intersectionForm_boundaryClass
      intersectionForm_isSymm intersectionForm_nondegenerate) boundaryClass_injective
    (fun i ↦ by simpa only [iso, LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv]
      using hforward g hj i)
    (fun i ↦ by simpa only [iso, LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv]
      using hforward h hj' i)
  have heq' := he.mpr ⟨hη, fun x hx ↦ by
    simpa only [coe_signedOrthogonalRestriction_apply, iso,
      LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv] using
      congrArg (fun a : K ≃ₗ[ℤ] K ↦ (a ⟨x, hx⟩ : Fin 10 → ℤ)) hres, rfl⟩
  apply Subtype.ext
  apply Prod.ext
  · exact (toIsometry_apply _ _ _).symm.trans
      ((iso.injective (congrArg Prod.fst heq')).trans (toIsometry_apply _ _ _))
  · exact (sign_apply _ _ _).symm.trans (hη.trans (sign_apply _ _ _))

local notation "invariants[" w "]" =>
  Quiver.Path.signedLoopInvariants w (fun j ↦ (exchangeKernelBasis j : Fin 4 → ℤ))
    boundaryOrders (boundaryOrders 0)

private theorem restriction_eq_exchangeKernelEquiv_iff (g : G) (w : Word B B) :
    LinearEquiv.autCongr e (res g).val = w.exchangeKernelEquiv ↔
      ∀ j, e ((res g).val (boundaryOrthogonalBasis j)) =
        w.exchangeKernelEquiv (exchangeKernelBasis j) := by
  constructor
  · intro h j
    simpa only [exchangeKernelBasis, Basis.map_apply, LinearEquiv.autCongr_apply_apply,
      LinearEquiv.symm_apply_apply] using congrArg (fun f : E ≃ₗ[ℤ] E ↦
        f (e (boundaryOrthogonalBasis j))) h
  · intro h
    apply LinearEquiv.toLinearMap_injective
    apply exchangeKernelBasis.ext
    intro j
    simpa only [LinearEquiv.coe_coe, exchangeKernelBasis, Basis.map_apply,
      LinearEquiv.autCongr_apply_apply, LinearEquiv.symm_apply_apply] using h j

/-- A loop and a signed Picard isometry have the same integer invariants precisely
when their signs, their actions in exchange-kernel coordinates, and their forward
images of component zero agree. -/
theorem picardInvariants_eq_signedLoopInvariants_iff (g : G) (w : Word B B) :
    picardInvariants g = invariants[w] ↔
      η g = (-1 : ℤˣ) ^ w.inversionCount ∧
      LinearEquiv.autCongr e (res g).val = w.exchangeKernelEquiv ∧
      ∃ j : Fin 8, (picard g).val (boundaryClass (label j)) = boundaryClass 0 ∧
        trop[w] (boundaryOrders 0) = boundaryOrders j := by
  have hmatrix :
      (picardInvariants g).kernelColumns =
          Matrix.of (fun i j ↦ w.exponentEquiv (exchangeKernelBasis j : Fin 4 → ℤ) i) ↔
        LinearEquiv.autCongr e (res g).val = w.exchangeKernelEquiv := by
    rw [restriction_eq_exchangeKernelEquiv_iff]
    refine ⟨fun h j ↦ Subtype.ext (funext fun i ↦ ?_), fun h ↦ Matrix.ext fun i j ↦ ?_⟩
    · simpa only [picardInvariants_kernelColumns_apply, Path.coe_exchangeKernelEquiv_apply,
        Matrix.of_apply] using congrFun (congrFun h i) j
    · simpa only [picardInvariants_kernelColumns_apply, Path.coe_exchangeKernelEquiv_apply,
        Matrix.of_apply] using congrArg (fun x : E ↦ (x : Fin 4 → ℤ) i) (h j)
  obtain ⟨j, hj⟩ := exists_picardInvariants_label g
  simp only [SignedLoopInvariants.ext_iff, picardInvariants_sign, Path.signedLoopInvariants_sign,
    Path.signedLoopInvariants_kernelColumns, Path.signedLoopInvariants_boundaryLabel, hmatrix]
  have hlabel := w.tropicalBoundaryLabel_eq_some_iff (boundaryOrders 0) boundaryOrders_injective
  refine and_congr_right (fun _ ↦ and_congr_right (fun _ ↦ ?_))
  constructor
  · intro heq
    exact ⟨j, (picardInvariants_label_eq_some_iff _ _).mp hj,
      ((hlabel j).mp (heq.symm.trans hj)).symm⟩
  · rintro ⟨k, hk, ht⟩
    exact ((picardInvariants_label_eq_some_iff _ _).mpr hk).trans
      ((hlabel k).mpr ht.symm).symm

/-- The quarter-turn is the unique signed Picard isometry with the integer
invariants of the rotation word. Its pullback shifts boundary classes by minus two. -/
theorem picardInvariants_eq_rotationWord_iff (g : G) :
    picardInvariants g = invariants[rotationWord] ↔ g = ι quarterTurn := by
  have heq : picardInvariants (ι quarterTurn) = invariants[rotationWord] := by
    refine (picardInvariants_eq_signedLoopInvariants_iff _ _).mpr
      ⟨by simp [inversionCount_rotationWord], (restriction_eq_exchangeKernelEquiv_iff _ _).mpr ?_,
        2, by simp [show label (2 : Fin 8) = 2 by decide],
        by simpa only [zero_add] using rotationWord_tropical_boundaryOrders 0⟩
    intro j
    apply (e).symm.injective
    rw [LinearEquiv.symm_apply_apply, exchangeKernelBasis_apply, rotationWord_exchangeKernelEquiv]
    suffices h : ![(Pi.single j 1 : Fin 2 → ℤ) 1, (Pi.single j 1 : Fin 2 → ℤ) 0] =
        Pi.single j.rev 1 by
      rw [h, ← exchangeKernelBasis_apply, exchangeKernelBasis, Basis.map_apply,
        LinearEquiv.symm_apply_apply]
      apply Subtype.ext
      simp
    revert j
    decide
  exact heq ▸ picardInvariants_injective.eq_iff

/-- The translation lift is the unique signed Picard isometry with the integer
invariants of the translation word. Its pullback shifts boundary classes by two. -/
theorem picardInvariants_eq_translationWord_iff (g : G) :
    picardInvariants g = invariants[translationWord] ↔ g = ι picardTranslation := by
  have heq : picardInvariants (ι picardTranslation) = invariants[translationWord] := by
    refine (picardInvariants_eq_signedLoopInvariants_iff _ _).mpr
      ⟨by simp [inversionCount_translationWord],
        (restriction_eq_exchangeKernelEquiv_iff _ _).mpr ?_,
        6, ?_, translationWord_tropical_boundaryOrders 0⟩
    · have h₀ : (res (ι picardTranslation)).val (boundaryOrthogonalBasis 0) =
          boundaryOrthogonalBasis 0 + (boundaryOrthogonalBasis 0 + boundaryOrthogonalBasis 1) := by
        apply Subtype.ext
        simpa only [coe_signedOrthogonalRestriction_apply, toIsometry_apply, sign_apply,
          coe_rotationInclusion, one_smul] using picardTranslation_boundaryOrthogonalBasis_zero
      have h₁ : (res (ι picardTranslation)).val (boundaryOrthogonalBasis 1) =
          -boundaryOrthogonalBasis 0 := by
        apply Subtype.ext
        simpa only [coe_signedOrthogonalRestriction_apply, toIsometry_apply, sign_apply,
          coe_rotationInclusion, one_smul, Submodule.coe_neg] using
          picardTranslation_boundaryOrthogonalBasis_one
      intro j
      rw [exchangeKernelBasis_apply, translationWord_exchangeKernelEquiv]
      fin_cases j
      · simp only [Fin.reduceFinMk, h₀, map_add,
          boundaryOrthogonalEquivExchangeKernel_apply_basis]
        rw [← map_add, ← map_add]
        exact congrArg exchangeKernelEquiv (by decide)
      · simp only [Fin.reduceFinMk, h₁, map_neg,
          boundaryOrthogonalEquivExchangeKernel_apply_basis]
        rw [← map_neg]
        exact congrArg exchangeKernelEquiv (by decide)
    · simp only [toIsometry_apply, coe_rotationInclusion, picardTranslation_boundaryClass]
      exact congrArg boundaryClass (by decide : label (6 : Fin 8) + 2 = 0)
  exact heq ▸ picardInvariants_injective.eq_iff

/-- The negative boundary reflection is the unique signed Picard isometry with
the integer invariants of the reflection word. Its underlying Picard action
fixes the orthogonal lattice, so the signed restriction acts by negation. -/
theorem picardInvariants_eq_reflectionWord_iff (g : G) :
    picardInvariants g = invariants[reflectionWord] ↔ g = boundaryReflection := by
  have heq : picardInvariants boundaryReflection = invariants[reflectionWord] := by
    refine (picardInvariants_eq_signedLoopInvariants_iff _ _).mpr
      ⟨by simp [inversionCount_reflectionWord], (restriction_eq_exchangeKernelEquiv_iff _ _).mpr ?_,
        6, by simp [show label (6 : Fin 8) = 6 by decide], reflectionWord_tropical_boundaryOrders 0⟩
    intro j
    rw [exchangeKernelBasis_apply, reflectionWord_exchangeKernelEquiv, map_neg,
      ← exchangeKernelBasis_apply, exchangeKernelBasis, Basis.map_apply, ← map_neg]
    apply congrArg e
    apply Subtype.ext
    simp
  exact heq ▸ picardInvariants_injective.eq_iff

section Generation

variable (k : Type*) [Field k]

local notation "Γ[" k "]" => ClusterModularGroup k B
local notation "Γ̂[" k "]" => SignedClusterModularGroup k B
local notation "eval[" k "," w "]" => op (signedClusterModularGroupMap k B (End.of w))
local notation "unsigned[" k "," w "," h "]" =>
  op (clusterModularGroupMap k B
    (Subtype.mk (End.of w) (Iff.mpr (mem_inversionFreeLoops_iff B (End.of w)) h)))

variable (ρ : Γ̂[k]ᵐᵒᵖ →* G) (hρ : Function.Injective ρ)

include hρ

/-- For a faithful signed Picard action, compatibility with the integer invariants
of the three explicit loops suffices to generate the group of signed X maps.
The generators are written in the opposite of the point-map group. -/
theorem closure_four_vertex_signed_words
    (hp : picardInvariants (ρ eval[k,rotationWord]) = invariants[rotationWord])
    (ht : picardInvariants (ρ eval[k,translationWord]) = invariants[translationWord])
    (hs : picardInvariants (ρ eval[k,reflectionWord]) = invariants[reflectionWord]) :
    Subgroup.closure ({eval[k,reflectionWord], eval[k,rotationWord], eval[k,translationWord]} :
      Set Γ̂[k]ᵐᵒᵖ) = ⊤ := by
  have hp' := (picardInvariants_eq_rotationWord_iff _).mp hp
  have ht' := (picardInvariants_eq_translationWord_iff _).mp ht
  have hs' := (picardInvariants_eq_reflectionWord_iff _).mp hs
  apply top_unique
  apply (Subgroup.map_le_map_iff_of_injective hρ).mp
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    hp', ht', hs', closure_four_vertex_signed_generators]
  exact le_top

/-- The rotation and translation generate all unsigned X maps once the faithful
Picard action has the indicated invariants for these loops and is positive on
the unsigned subgroup. -/
theorem closure_four_vertex_unsigned_words
    (hpos : ∀ f : Γ[k]ᵐᵒᵖ, η (ρ ((clusterModularGroupInclusion k B).op f)) = 1)
    (hp : picardInvariants (ρ eval[k,rotationWord]) = invariants[rotationWord])
    (ht : picardInvariants (ρ eval[k,translationWord]) = invariants[translationWord]) :
    Subgroup.closure ({unsigned[k,rotationWord, inversionCount_rotationWord],
      unsigned[k,translationWord, inversionCount_translationWord]} : Set Γ[k]ᵐᵒᵖ) = ⊤ := by
  let f := ρ.comp (clusterModularGroupInclusion k B).op
  have hfinj : Function.Injective f := hρ.comp
    (op_injective.comp ((clusterModularGroupInclusion_injective k B).comp unop_injective))
  have hp' : f unsigned[k,rotationWord, inversionCount_rotationWord] = ι quarterTurn := by
    simpa only [f, MonoidHom.comp_apply, MonoidHom.op_apply_apply, Function.comp_apply, unop_op,
      clusterModularGroupInclusion_clusterModularGroupMap] using
      (picardInvariants_eq_rotationWord_iff _).mp hp
  have ht' : f unsigned[k,translationWord, inversionCount_translationWord] =
      ι picardTranslation := by
    simpa only [f, MonoidHom.comp_apply, MonoidHom.op_apply_apply, Function.comp_apply, unop_op,
      clusterModularGroupInclusion_clusterModularGroupMap] using
      (picardInvariants_eq_translationWord_iff _).mp ht
  apply top_unique
  apply (Subgroup.map_le_map_iff_of_injective hfinj).mp
  rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, hp', ht',
    ← Set.image_pair, ← MonoidHom.map_closure, closure_four_vertex_rotation_generators,
    ← MonoidHom.range_eq_map (ι), range_rotationInclusion]
  rintro _ ⟨g, _, rfl⟩
  exact MonoidHom.mem_ker.mpr (hpos g)

end Generation

end QPainleve.FourVertex
