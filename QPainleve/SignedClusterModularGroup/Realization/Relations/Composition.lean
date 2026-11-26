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

open AlgebraicGeometry CategoryTheory DihedralGroup MulOpposite Quiver
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
      ⟨(invariant v).sign * (invariant w).sign,
        (invariant w).kernelColumns * (read * (invariant v).kernelColumns), do
          let j ← (invariant w).boundaryLabel
          let k ← (invariant v).boundaryLabel
          pure (index.symm ((invariant v).sign • index j + index k))⟩ := by
  intro index orders invariant
  let d := M₀.boundaryClass cartier[M₀]
  obtain ⟨A⟩ := Q.nonempty_signedLoopPicardComparison_of_nodal_contraction
    p₀ hnodal₀ hE hprim hnef hsq
  let Θ := A.identification.signedEquiv
  obtain ⟨j, hj, hw⟩ := A.boundaryLabel_spec w
  obtain ⟨k, hk, hv⟩ := A.boundaryLabel_spec v
  obtain ⟨l, hl, hcomp⟩ := A.boundaryLabel_spec (w.comp v)
  have hD := M₀.boundaryClass_injective_of_nef_square_zero cartier[M₀] hnef hsq
  let action := boundaryAction B d hD
  have label_eq (u : Word E E) (a : Fin n)
      (ha : ∀ i, (toIsometry B d (Θ eval[u])).val (d i) =
        d (sign B d (Θ eval[u]) • (i - index a))) :
      cycleVertexPerm (action (op (Θ eval[u]))) 0 = index a :=
    (cycleVertexPerm_boundaryAction_apply_eq_iff B d hD _ _ _).mpr (by simpa using ha (index a))
  have hprod : Θ eval[w.comp v] = Θ eval[w] * Θ eval[v] := by
    -- Endomorphism multiplication executes the right-hand path first.
    have hEnd : (End.of (w.comp v) : End ((Paths.of (SkewExchangeMatrix (Fin r))).obj E)) =
        End.of v * End.of w := rfl
    rw [hEnd, map_mul, op_mul, map_mul]
  have hs : (invariant v).sign = sign B d (Θ eval[v]) := by
    simp only [invariant, Path.signedLoopInvariants_sign, SignedBoundaryIsometryGroup.sign_apply, Θ,
      A.identification.sign_signedEquiv_apply_word]
  have hlabel : index l = (invariant v).sign • index j + index k := by
    calc
      index l = cycleVertexPerm (action (op (Θ eval[w.comp v]))) 0 :=
        (label_eq _ _ hcomp).symm
      _ = cycleVertexPerm (action (op (Θ eval[v]))) (index j) := by
        rw [hprod, op_mul, map_mul, map_mul, Equiv.Perm.mul_apply, label_eq _ _ hw]
      _ = _ := by
        rw [cycleVertexPerm_apply, ← Units.smul_def, label_eq _ _ hv, hs]
        exact congrArg (fun η : ℤˣ ↦ η • index j + index k)
          (cycleOrientationSign_boundaryAction B d hD _)
  refine SignedLoopInvariants.ext ?_ ?_ ?_
  · simp only [invariant, Path.signedLoopInvariants_sign, Path.inversionCount_comp, pow_add]
    exact mul_comm _ _
  · exact Path.signedLoopInvariants_comp_matrix w v β orders (orders 0) read hread
  · simpa only [invariant, Path.signedLoopInvariants_boundaryLabel, orders, hj, hk, hl,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def] using
      congrArg some (index.eq_symm_apply.mpr hlabel)

end QPainleve.SignedClusterModularGroup.CompleteToricPresentation
