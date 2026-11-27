/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Endpoint
public import QPainleve.SignedClusterModularGroup.Realization.Agreement

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
import QPainleve.SignedClusterModularGroup.Realization.Boundary

/-!
# Numerical invariants of contracted toric fibers

A nodal blowup tower presenting a contracted toric fiber gives projectivity of
the toric base. For a primitive nef square-zero anticanonical cycle, it also
determines the ranks and bounds the index of the charge lattice.
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme.IdealSheafData LineBundleClass TauCeti.Toric.Fan

namespace QPainleve.SignedClusterModularGroup.ContractedToricFiber

variable {k : Type} [Field k] [IsAlgClosed k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing k (Fin r)))
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.toricBoundaryIdeal k Φ h)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "Pic[" Φ "," r "]" =>
  Additive (LineBundleClass (Fan.finiteFanScheme k Φ)) × (Fin r → ℤ)
local notation "centers(" c ")" => (fun j ↦ c (ofAdd (Pi.single j 1)))
local notation "model[" b "," s "," c "]" => Fan.internalBlowupTower k b s centers(c)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}
  [hΦ₀ : Nonempty Φ.cones]
  {r n m : ℕ} [NeZero n] [NeZero m]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {M : MarkedSurface k n B (Spec (.of (LaurentRing k (Fin r))))}
  {b : Basis (Fin 2) ℤ N}
  {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily ((Φ.toricBoundaryIdeal k hΦ₀).subscheme ↘ Spec (.of k))]
  {α : Type*} {a : α → ((Φ.toricBoundaryIdeal k hΦ₀).subscheme ↘ Spec (.of k)).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m}
  {o : ZMod m} {J : L →ₗ[ℤ] Additive (LineBundleClass (Φ.finiteFanScheme k)) × (Fin r → ℤ)}
  {c : Multiplicative (Fin r → ℤ) →* kˣ}
  (p : ContractedToricFiber b s hΦ T o J c M)

local instance : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
local instance : M.surface.IsProjectiveOver k := M.projective
local instance : PrestableFamily (D[M].subscheme ↘ S) := M.prestable_boundaryImage

include p in
/-- The toric base of a marked presentation is projective when its contraction
is identified with a specified blowup tower over the projective pair. -/
theorem isProjectiveOver_toricBase {l : ℕ} {Y : Scheme} {A : BlowupTower M.surface l Y}
    (u : Y ≅ (model[b,s,c]).1) (hu : u.inv ≫ A.toBase = p.projection) :
    (Φ.finiteFanScheme k).IsProjectiveOver k := by
  let P := model[b,s,c]
  let : Y.Over S := ⟨A.toBase ≫ (M.surface ↘ S)⟩
  let : Y.IsProjectiveOver k := A.isProjectiveOver k
  let : P.1.Over S := ⟨P.2.toTower.toBase ≫ ((Φ.finiteFanScheme k) ↘ S)⟩
  have hover : u.inv ≫ A.toBase ≫ (M.surface ↘ S) =
      P.2.toTower.toBase ≫ ((Φ.finiteFanScheme k) ↘ S) := by
    rw [← Category.assoc, hu, p.projection_over, finiteFanScheme_over]
  let : u.inv.IsOver S := ⟨hover⟩
  have hP : P.1.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k u.inv
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme k) ↘ S) := by
    rw [finiteFanScheme_over]
    exact hdim ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  exact (isClosedPointTower_internalBlowupTower k b s centers(c)).isProjectiveOver_base hP

include p in
/-- The charge lattice of a contracted nodal toric model of a primitive nef
square-zero anticanonical cycle has rank two and index at most three. The
number of centers and the rank of the charge kernel are fixed by the cycle length. -/
theorem chargeIndex_bounds_of_anticanonical_cycle
    [Scheme.IsRationalOver (M.surface ↘ S)]
    (hcΦ : Φ.IsComplete)
    {l : ℕ} {Y : Scheme} {A : BlowupTower M.surface l Y}
    (hA : IsNodalBoundaryTower D[M] (M.surface ↘ S) (𝟙 _) A)
    (u : Y ≅ (model[b,s,c]).1) (hu : u.inv ≫ A.toBase = p.projection)
    (hD : D[M].IsEffectiveCartier) (hnefD : IsNef k (M.surface ↘ S) classOf(hD))
    (hsqD : Chow.classIntersectionNumber k M.surface classOf(hD) classOf(hD) = 0)
    (hcan : classOf(hD) = (LineBundleClass.mk (canonicalBundle k M.surface 2))⁻¹)
    (hδ : IsPrimitive (Additive.ofMul classOf(hD))) :
    r + n = 12 ∧ Module.finrank ℤ (Fan.rayChargeMap s).ker = 10 - n ∧
      Module.finrank ℤ (Fan.rayChargeMap s).range = 2 ∧
      n ≤ 9 ∧ (Fan.rayChargeMap s).range.toAddSubgroup.index ^ 2 ∣ n ∧
      (Fan.rayChargeMap s).range.toAddSubgroup.index ∈ ({1, 2, 3} : Finset ℕ) ∧
      ∃ x : (Fan.rayChargeMap s).ker, TauCeti.IsPrimitive x ∧
        ((Fan.rayChargeMap s).range.toAddSubgroup.index : ℤ) ∣ ∑ j, x.val j ^ 2 := by
  let : IsNoetherian M.surface := isNoetherian_of_finiteType (M.surface ↘ S)
  let D := M.imageCycle
  let P := (D.boundaryPrimeEquiv hD).toEmbedding.trans (D[M]).boundaryPrimeEmbedding
  let Q : ZMod n ↪ M.surface := ⟨D.ambientNode, D.ambientNode_injective⟩
  have hp (x : CodimensionOnePoint M.surface) :
      (x : M.surface) ∈ D[M].support ↔ x ∈ Set.range P := by
    simp only [P, Function.Embedding.coe_trans, Equiv.coe_toEmbedding,
      (D.boundaryPrimeEquiv hD).surjective.range_comp, range_boundaryPrimeEmbedding]
    rfl
  have hinc (i j : ZMod n) (hij : i ≠ j) :
      closure {(P i : M.surface)} ∩ closure {(P j : M.surface)} =
        Q '' {a | (a = i ∧ j = i + 1) ∨ (a = j ∧ i = j + 1)} := by
    simpa only [P, Q, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Function.Embedding.coeFn_mk, coe_boundaryPrimeEmbedding] using
      D.closure_boundaryPrime_inter_of_ne hD hij
  have hnodal : AtWorstNodalOfRelativeDimensionOne (D[M].subscheme ↘ S) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have hprojective : (Φ.finiteFanScheme k).IsProjectiveOver k :=
    p.isProjectiveOver_toricBase u hu
  have he : u.inv ≫ A.toBase ≫ (M.surface ↘ S) =
      (model[b,s,c]).2.toTower.toBase ≫ ((Φ.finiteFanScheme k) ↘ S) := by
    rw [← Category.assoc, hu, p.projection_over, Fan.finiteFanScheme_over]
  have hs : ((D[M].comap A.toBase).comap u.inv).support =
      (model[b,s,c]).2.boundaryι.ker.support := by
    rw [← comap_comp, hu, p.support_comap]
  clear hu
  revert u he hs
  rw [Fan.internalBlowupTower_eq_alongBoundary]
  intro u he hs
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  exact Fan.chargeIndex_bounds_of_nodal_anticanonical_cycle k hΦ hdim s
    (fun j ↦ (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom)
    (fun _ ↦ b.detDualEquiv_self _) (fun j ↦ (s j).surjective_detCharacter b) centers(c)
    (fun j ↦ (s j).internalCenter k b (centers(c) j))
    (fun j ↦ (s j).internalCenter_val k b (centers(c) j)) hA u he hs hcΦ
    hD hnodal hnefD hsqD hcan hδ P Q hp hinc

end QPainleve.SignedClusterModularGroup.ContractedToricFiber
