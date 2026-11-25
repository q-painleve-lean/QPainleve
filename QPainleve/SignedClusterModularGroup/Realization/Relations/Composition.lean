/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Relations.PicardAction

/-!
# Composition of the integer invariants of signed loops

The invariant of a concatenation can be obtained from the two invariants by
matrix multiplication and the affine action on boundary labels. Kernel exponents
are pulled back in reverse execution order, while boundary labels are transported
forward. The boundary comparison uses the signed Picard equivalence of the same
marked nodal contraction for both loops.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Quiver
open QPainleve.CharacterTorus QPainleve.Cluster QPainleve.SignedBoundaryIsometryGroup
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup.CompleteToricPresentation

open GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹
local notation "eval[" w "]" => op (signedClusterModularGroupMap ℂ _ (End.of w))

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Module.Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {E : SkewExchangeMatrix (Fin r)}
  (Q : CompleteToricPresentation i b r L γ)
  {c₀ : Point Centers[r]} {M₀ : MarkedSurface ℂ n B XTor[r]}

local instance instNonemptyCompositionCones : Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroCompositionBoundaryLength : NeZero Q.length := Q.neZero
local instance instPrestableCompositionToricBoundary :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "fiber[" M "," c "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M
local notation "K" => E.matrix.mulVecLin.ker

/-- The complete integer invariant of `w` followed by `v` is obtained from their
inversion signs, ambient Casimir columns, and forward boundary labels. The matrix
`read` recovers basis coordinates from ambient columns. On the boundary the second
loop sends the first loop's label `j` to `η_v • j + j_v`, including on cycles with
one or two components. -/
theorem signedLoopInvariants_comp_of_nodal_contraction
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hprim : IsPrimitive (Additive.ofMul classOf(cartier[M₀])))
    (hnef : (classOf(cartier[M₀])).IsNef ℂ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber ℂ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    {κ : Type*} [Fintype κ] [DecidableEq κ] (β : Module.Basis κ ℤ K)
    (read : Matrix κ (Fin r) ℤ) (hread : read * Matrix.of (fun i j ↦ (β j : Fin r → ℤ) i) = 1)
    (w v : Word E E) :
    let index := (ZMod.finEquiv n).toEquiv
    let orders := p₀.numberedBoundaryOrders cartier[M₀]
    let invariant (u : Word E E) :=
      u.signedLoopInvariants (fun j ↦ (β j : Fin r → ℤ)) orders (orders 0)
    invariant (w.comp v) =
      ((invariant v).1 * (invariant w).1, (invariant w).2.1 * (read * (invariant v).2.1), do
        let j ← (invariant w).2.2
        let k ← (invariant v).2.2
        pure (index.symm ((invariant v).1 • index j + index k))) := by
  intro index orders invariant
  let d := M₀.boundaryClass cartier[M₀]
  obtain ⟨_, _, _, Θ, _, _, _, _, _, _, hInv⟩ :=
    Q.exists_picardEquiv_signedLoopInvariants_of_nodal_contraction p₀ hnodal₀ hE hprim hnef hsq
  obtain ⟨j, hj, hw⟩ := hInv w β
  obtain ⟨k, hk, hv⟩ := hInv v β
  obtain ⟨l, hl, hcomp⟩ := hInv (w.comp v) β
  have hprod : Θ eval[w.comp v] = Θ eval[w] * Θ eval[v] := by
    -- Endomorphism multiplication executes the right-hand path first.
    have hEnd : (End.of (w.comp v) : End ((Paths.of (SkewExchangeMatrix (Fin r))).obj E)) =
        End.of v * End.of w := rfl
    rw [hEnd, map_mul, op_mul, map_mul]
  have hw₀ : (toIsometry B d (Θ eval[w])).val (d (index j)) = d 0 := by
    simpa only [index, sub_self, smul_zero] using hw (index j)
  have hl₀ : (toIsometry B d (Θ eval[w.comp v])).val (d (index l)) = d 0 := by
    have h := hcomp ((ZMod.finEquiv n).toEquiv l)
    rw [sub_self, smul_zero] at h
    exact h
  let p := sign B d (Θ eval[v]) • index j + index k
  have hvp : (toIsometry B d (Θ eval[v])).val (d p) = d (index j) := by
    simpa only [p, index, d, add_sub_cancel_right, smul_smul, Int.units_mul_self, one_smul]
      using hv p
  have hp : (toIsometry B d (Θ eval[w.comp v])).val (d p) = d 0 := by
    rw [hprod, map_mul, Subgroup.coe_mul, mul_apply_eq_comp, hvp, hw₀]
  have hD := M₀.boundaryClass_injective_of_nef_square_zero cartier[M₀] hnef hsq
  have hlp : l = index.symm p := by
    apply index.injective
    rw [Equiv.apply_symm_apply]
    exact hD ((toIsometry B d (Θ eval[w.comp v])).val.injective (hl₀.trans hp.symm))
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [invariant, Path.signedLoopInvariants_def, Path.inversionCount_comp, pow_add]
    exact mul_comm _ _
  · exact Path.signedLoopInvariants_comp_matrix w v β orders (orders 0) read hread
  · have hj' : (invariant w).2.2 = some j := congrArg (fun t ↦ t.2.2) hj
    have hk' : (invariant v).2.2 = some k := congrArg (fun t ↦ t.2.2) hk
    have hl' : (invariant (w.comp v)).2.2 = some l := congrArg (fun t ↦ t.2.2) hl
    have hs : (invariant v).1 = sign B d (Θ eval[v]) := congrArg Prod.fst hk
    rw [hj', hk', hl', hs, hlp]
    rfl

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
