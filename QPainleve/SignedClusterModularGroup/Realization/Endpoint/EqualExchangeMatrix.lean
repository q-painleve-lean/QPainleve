/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Boundary.CommonRefinement
public import QPainleve.SignedClusterModularGroup.Realization.Endpoint.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Projective
import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
import QPainleve.SignedClusterModularGroup.Realization.Boundary

/-!
# Marked endpoints with equal exchange matrices

The primitive anticanonical cycle determines the extension of the labeled
charge correspondence to the ambient lattice. Using a common oriented toric
refinement, the resulting comparison of endpoints preserves the ordered
branches and reads the full Picard pullback in fixed toric coordinates.

The integral extension uses `Fan.existsUnique_rayChargeEquiv_of_anticanonical_cycle`.
The comparison after extension uses `ContractedToricFiber.exists_marked_toric_endpoint_comparison`.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Module Multiplicative TopologicalSpace
open QPainleve.BlowupTower QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme.IdealSheafData LineBundleClass TauCeti.Toric.Fan

namespace QPainleve.SignedClusterModularGroup.ContractedToricFiber

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Xtor[" r "]" => Spec (CommRingCat.of (LaurentRing ℂ (Fin r)))
local notation "Dtor[" Φ "," h "]" => Scheme.IdealSheafData.subscheme (Fan.boundaryIdeal Φ h)
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "Pic[" Φ "," r "]" =>
  Additive (LineBundleClass (Fan.algebraicRealization Φ)) × (Fin r → ℤ)
local notation "centers(" c ")" => (fun j ↦ c (ofAdd (Pi.single j 1)))
local notation "model[" b "," s "," c "]" => Fan.internalBlowupTower b s centers(c)
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "renameX(" σ ")" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (LaurentRing.rename (R := ℂ) (Equiv.toFun σ))))

variable {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [hΦ₀ : Nonempty Φ.cones]
  {r n m : ℕ} [NeZero n] [NeZero m]
  {L : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {M : MarkedSurface ℂ n B Xtor[r]}
  {b : Basis (Fin 2) ℤ N} {b' : Basis (Fin 2) ℤ N'}
  {s : Fin r → Φ.Ray} {s' : Fin r → Ψ.Ray} {hΦ : Φ.IsRegular}
  [PrestableFamily (Dtor[Φ,hΦ₀] ↘ S)]
  {α : Type*} {a : α → (Dtor[Φ,hΦ₀] ↘ S).smoothLocus}
  {T : Scheme.NodalCycleNumbering a m}
  {o : ZMod m} {J : L →ₗ[ℤ] Pic[Φ,r]}
  {c : Multiplicative (Fin r → ℤ) →* ℂˣ}
  (p : ContractedToricFiber b s hΦ T o J c M)

local instance : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
local instance : M.surface.IsProjectiveOver ℂ := M.projective
local instance : PrestableFamily (D[M].subscheme ↘ S) := M.prestable_boundaryImage

include p in
/-- The toric base of a marked presentation is projective when its contraction
is identified with a specified blowup tower over the projective pair. -/
theorem isProjectiveOver_toricBase {l : ℕ} {Y : Scheme} {A : BlowupTower M.surface l Y}
    (u : Y ≅ (model[b,s,c]).1) (hu : u.inv ≫ A.toBase = p.projection) :
    Φ.algebraicRealization.IsProjectiveOver ℂ := by
  let P := model[b,s,c]
  let : Y.Over S := ⟨A.toBase ≫ (M.surface ↘ S)⟩
  let : Y.IsProjectiveOver ℂ := A.isProjectiveOver ℂ
  let : P.1.Over S := ⟨P.2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S)⟩
  have hover : u.inv ≫ A.toBase ≫ (M.surface ↘ S) =
      P.2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S) := by
    rw [← Category.assoc, hu, p.projection_over, algebraicRealization_over]
  let : u.inv.IsOver S := ⟨hover⟩
  have hP : P.1.IsProjectiveOver ℂ := Scheme.IsProjectiveOver.of_isClosedImmersion ℂ u.inv
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : SmoothOfRelativeDimension 2 (Φ.algebraicRealization ↘ S) := by
    rw [algebraicRealization_over]
    exact hdim ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  exact (isClosedPointTower_internalBlowupTower b s centers(c)).isProjectiveOver_base hP

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
    (hD : D[M].IsEffectiveCartier) (hnefD : IsNef ℂ (M.surface ↘ S) classOf(hD))
    (hsqD : Chow.classIntersectionNumber ℂ M.surface classOf(hD) classOf(hD) = 0)
    (hcan : classOf(hD) = (LineBundleClass.mk (canonicalBundle ℂ M.surface 2))⁻¹)
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
  have hprojective : Φ.algebraicRealization.IsProjectiveOver ℂ :=
    p.isProjectiveOver_toricBase u hu
  have he : u.inv ≫ A.toBase ≫ (M.surface ↘ S) =
      (model[b,s,c]).2.toTower.toBase ≫ (Φ.algebraicRealization ↘ S) := by
    rw [← Category.assoc, hu, p.projection_over, Fan.algebraicRealization_over]
  have hs : ((D[M].comap A.toBase).comap u.inv).support =
      (model[b,s,c]).2.boundaryι.ker.support := by
    rw [← comap_comp, hu, p.support_comap]
  clear hu
  revert u he hs
  rw [Fan.internalBlowupTower_eq_alongBoundary]
  intro u he hs
  have hdim := (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  exact Fan.chargeIndex_bounds_of_nodal_anticanonical_cycle hΦ hdim s
    (fun j ↦ (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom)
    (fun _ ↦ b.detDualEquiv_self _) (fun j ↦ (s j).surjective_detCharacter b) centers(c)
    (fun j ↦ (s j).internalCenter b (centers(c) j))
    (fun j ↦ (s j).internalCenter_val b (centers(c) j)) hA u he hs hcΦ
    hD hnodal hnefD hsqD hcan hδ P Q hp hinc

include p in
/-- An equal exchange matrix identifies the ambient lattice of an ordered presentation
of a primitive nef square-zero anticanonical cycle. The equivalence is unique,
sends each labeled primitive ray to its counterpart, and preserves the determinant. -/
theorem existsUnique_rayChargeEquiv_of_equal_exchange_matrix
    [Scheme.IsRationalOver (M.surface ↘ S)]
    (hcΦ : Φ.IsComplete)
    {l : ℕ} {Y : Scheme} {A : BlowupTower M.surface l Y}
    (hA : IsNodalBoundaryTower D[M] (M.surface ↘ S) (𝟙 _) A)
    (u : Y ≅ (model[b,s,c]).1) (hu : u.inv ≫ A.toBase = p.projection)
    (hD : D[M].IsEffectiveCartier) (hnefD : IsNef ℂ (M.surface ↘ S) classOf(hD))
    (hsqD : Chow.classIntersectionNumber ℂ M.surface classOf(hD) classOf(hD) = 0)
    (hcan : classOf(hD) = (LineBundleClass.mk (canonicalBundle ℂ M.surface 2))⁻¹)
    (hδ : IsPrimitive (Additive.ofMul classOf(hD)))
    (hmat : chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (rayChargeMap s')) :
    ∃! E : N ≃ₗ[ℤ] N', (∀ j, E (s j).primitiveGenerator = (s' j).primitiveGenerator) ∧
      ∀ x y, b'.detDualEquiv (E x) (E y) = b.detDualEquiv x y := by
  obtain ⟨hcount, _, _, hk, hindex, _, hrel⟩ :=
    p.chargeIndex_bounds_of_anticanonical_cycle hcΦ hA u hu hD hnefD hsqD hcan hδ
  exact Fan.existsUnique_rayChargeEquiv_of_index s s' b b' hmat hcount hk hindex hrel

variable [hΨ₀ : Nonempty Ψ.cones] {m' : ℕ} [NeZero m']
  {L' : Type} [AddCommGroup L'] {B' : LinearMap.BilinForm ℤ L'}
  {M' : MarkedSurface ℂ n B' Xtor[r]} {hΨ : Ψ.IsRegular}
  [PrestableFamily (Dtor[Ψ,hΨ₀] ↘ S)]
  {α' : Type*} {a' : α' → (Dtor[Ψ,hΨ₀] ↘ S).smoothLocus}
  {T' : Scheme.NodalCycleNumbering a' m'} {o' : ZMod m'} {J' : L' →ₗ[ℤ] Pic[Ψ,r]}
  {d : Multiplicative (Fin r → ℤ) →* ℂˣ}
  (q : ContractedToricFiber b' s' hΨ T' o' J' d M')

include p q in
/-- Equal exchange matrices and matched ordered centers give a marked comparison of
the endpoint pairs. The construction produces the determinant-preserving lattice
identification and a common oriented refinement. The resulting rotation on the
ordered branches and the full Picard pullback are computed on that refinement. -/
theorem exists_marked_endpoint_comparison_of_equal_exchange_matrix
    [Scheme.IsRationalOver (M.surface ↘ S)]
    (hcΦ : Φ.IsComplete) (hcΨ : Ψ.IsComplete)
    (v : ZMod m ≃ Φ.Ray) (v' : ZMod m' ≃ Ψ.Ray)
    (hv : ∀ j, T.component j = Φ.boundaryNormalizationComponentEquiv hΦ (v j))
    (hv' : ∀ j, T'.component j = Ψ.boundaryNormalizationComponentEquiv hΨ (v' j))
    (hpos : ∀ j, b.detDualEquiv (v j).primitiveGenerator (v (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Φ.cones, (v j).toCone ≤ σ ∧ (v (j + 1)).toCone ≤ σ)
    (hpos' : ∀ j, b'.detDualEquiv (v' j).primitiveGenerator (v' (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Ψ.cones, (v' j).toCone ≤ σ ∧ (v' (j + 1)).toCone ≤ σ)
    (σ : Equiv.Perm (Fin r)) (hc : centers(d) ∘ σ = centers(c))
    (horder : ∀ j l, j < l → σ l < σ j →
      (s' (σ j), centers(d) (σ j)) ≠ (s' (σ l), centers(d) (σ l)))
    {l l' : ℕ} {Y Y' : Scheme}
    {A : BlowupTower M.surface l Y} {A' : BlowupTower M'.surface l' Y'}
    (hA : IsNodalBoundaryTower D[M] (M.surface ↘ S) (𝟙 _) A)
    (hA' : IsNodalBoundaryTower D[M'] (M'.surface ↘ S) (𝟙 _) A')
    (u : Y ≅ (model[b,s,c]).1) (u' : Y' ≅ (model[b',s',d]).1)
    (hu : u.inv ≫ A.toBase = p.projection) (hu' : u'.inv ≫ A'.toBase = q.projection)
    (hD : D[M].IsEffectiveCartier) (hE : D[M'].IsEffectiveCartier)
    (hnefD : IsNef ℂ (M.surface ↘ S) classOf(hD))
    (hnefE : IsNef ℂ (M'.surface ↘ S) classOf(hE))
    (hsqD : Chow.classIntersectionNumber ℂ M.surface classOf(hD) classOf(hD) = 0)
    (hsqE : Chow.classIntersectionNumber ℂ M'.surface classOf(hE) classOf(hE) = 0)
    (hcan : classOf(hD) = (LineBundleClass.mk (canonicalBundle ℂ M.surface 2))⁻¹)
    (hδ : IsPrimitive (Additive.ofMul classOf(hD)))
    (hmat : chargeExchangeMatrix b.detDualEquiv.toLinearMap (rayChargeMap s) =
      chargeExchangeMatrix b'.detDualEquiv.toLinearMap (rayChargeMap (s' ∘ σ))) :
    ∃ e : N ≃ₗ[ℤ] N',
      (∀ j, e (s j).primitiveGenerator = (s' (σ j)).primitiveGenerator) ∧
      (∀ x y, b'.detDualEquiv (e x) (e y) = b.detDualEquiv x y) ∧
      let g := Ψ.mapEquivIso Φ.lattice e.symm
      let hΩ₀ := Nonempty.map g.coneEquiv hΨ₀
      ∃ (Δ : Fan i) (hΔΦ : Δ.IsSubdivision Φ)
        (hΔΩ : Δ.IsSubdivision (Ψ.mapEquiv Φ.lattice e.symm)),
        let hΔ₀ := hΔΦ.nonempty_cones_of_nonempty hΦ₀
        let left := hΔΦ.boundaryMap hΔ₀ hΦ₀
        let right := hΔΩ.boundaryMap hΔ₀ hΩ₀ ≫ (g.boundaryIso hΨ₀ hΩ₀).inv
        ∃ (I : B'.IsometryEquiv B) (j : ZMod n)
          (R : FiberRealization M M' (renameX(σ.symm)).toRationalMap I (DihedralGroup.r j)),
          (left ≫ p.boundaryMap) ≫ (MarkedSurface.boundaryIso R.iso).hom =
            right ≫ q.boundaryMap ∧
          (∀ (x : L) (y : L'), I y = x ↔
            (Additive.ofMul (pullback hΔΦ.toFanHom.algebraicMap (J x).1.toMul), (J x).2) =
            (Additive.ofMul (pullback
              (hΔΩ.toFanHom.algebraicMap ≫ g.symm.toFanHom.algebraicMap) (J' y).1.toMul),
              (J' y).2 ∘ σ)) ∧
          (letI : PrestableFamily (M.boundary ↘ S) := M.prestable
           letI : PrestableFamily (M'.boundary ↘ S) := M'.prestable
           ∀ x : Dtor[Δ,hΔ₀], left x = T.componentGenericPoint o →
               (right ≫ q.boundaryMap) x = M'.cycle.componentGenericPoint j) := by
  obtain ⟨e, ⟨hmatch, hdet⟩, -⟩ := p.existsUnique_rayChargeEquiv_of_equal_exchange_matrix
    (s' := s' ∘ σ) hcΦ hA u hu hD hnefD hsqD hcan hδ hmat
  let g := Ψ.mapEquivIso Φ.lattice e.symm
  have hg (x y : N') : b.detDualEquiv (g.latticeEquiv x) (g.latticeEquiv y) =
      b'.detDualEquiv x y := by
    simpa only [g, Fan.mapEquivIso_latticeEquiv, LinearEquiv.coe_addEquiv_apply,
      LinearEquiv.apply_symm_apply] using (hdet (e.symm x) (e.symm y)).symm
  obtain ⟨Δ, hΔΦ, hΔΩ, hΔ, hpre, k, hk, U, hleft, hright⟩ :=
    g.exists_oriented_common_boundary_subdivision T T' hΦ hΨ hcΦ hcΨ hv hv' b b' hg hpos hpos'
  let : NeZero k := hk
  let : PrestableFamily (Dtor[Δ,hΔΦ.nonempty_cones_of_nonempty hΦ₀] ↘ S) := hpre
  exact ⟨e, hmatch, hdet, Δ, hΔΦ, hΔΩ,
    p.exists_marked_toric_endpoint_comparison q e hΔΦ hΔΩ hΔ σ hc hmatch hdet horder hA hA'
      u u' hu hu' hD hE hnefD hnefE hsqD hsqE U hleft hright⟩

end QPainleve.SignedClusterModularGroup.ContractedToricFiber
