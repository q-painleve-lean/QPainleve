/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.ChargeKernel.Action
public import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.Relations

import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
import QPainleve.SignedClusterModularGroup.Examples.ElevenVertex.Presentation
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Reference
import QPainleve.SignedClusterModularGroup.Realization.Relations.Casimir

/-!
# Deciding relations of the eleven-vertex seed

The ordered plane blowups give a marked reference model with one boundary component.
The squarefree-boundary relation criterion then reduces equality of independent X pullbacks to
transport of the nine explicit integral Casimir basis vectors. The algorithm uses the
original seed labels, including when the reference model uses the transposed lattice frame.
The same criterion proves faithfulness of the signed group's exchange-kernel action.

The proof uses `exists_marked_reference_fiber_of_ordered_towers` and
`CompleteToricPresentation.xPullback_eq_iff_exponentEquiv_eq_on_basis_of_squarefree`.
-/

public section

open CategoryTheory MulOpposite Quiver QPainleve.Cluster

namespace QPainleve.ElevenVertex

local notation "B" => exchangeMatrix
local notation "K" => exchangeMatrix.matrix.mulVecLin.ker

private def transportedColumns {E : SkewExchangeMatrix (Fin 11)} (w : Word E E) :
    Fin 9 → Fin 11 → ℤ :=
  fun j ↦ w.exponentEquiv (exchangeKernelBasisVectors j)

variable (k : Type*) [Field k]

private theorem xPullback_eq_iff_columns_of_neg
    (h : ∀ w v : Word (-B) (-B),
      w.xPullback k = v.xPullback k ↔ transportedColumns w = transportedColumns v)
    (w v : Word B B) :
    w.xPullback k = v.xPullback k ↔ transportedColumns w = transportedColumns v := by
  let s : B ⟶ -B := (Generator.invert.toStep B).cast rfl (Generator.target_invert B)
  let u (p : Word B B) := (s.toPath.reverse.comp p).comp s.toPath
  have hX (p : Word B B) : (u p).xPullback k =
      ((s.toPath.xPullback k)⁻¹ * p.xPullback k) * s.toPath.xPullback k := by
    simp [u]
  have hexp (p : Word B B) (x : Fin 11 → ℤ) :
      (u p).exponentEquiv x = p.exponentEquiv x := by
    have hs : s.exponentEquiv = LinearEquiv.neg ℤ := by simp [s]
    have hs' : Step.exponentEquiv (Quiver.reverse s) = LinearEquiv.neg ℤ := by
      rw [Step.exponentEquiv_eq]
      simp [Step.reverse_generator, s]
    simp [u, Path.reverse_toPath, hs, hs']
  have hcols (p : Word B B) : transportedColumns (u p) = transportedColumns p :=
    funext fun j ↦ hexp p (exchangeKernelBasisVectors j)
  simpa only [hX, mul_left_cancel_iff, mul_right_cancel_iff, hcols] using h (u w) (u v)

variable [CharZero k]

open AlgebraicGeometry QPainleve.SignedClusterModularGroup TauCeti
open TauCeti.AlgebraicGeometry TauCeti.Toric Scheme.IdealSheafData

private theorem neg_exchangeMatrix_eq_chargeExchangeMatrix :
    (-B).matrix = chargeExchangeMatrix
      ((Pi.basisFun ℤ (Fin 2)).reindex (Equiv.swap 0 1)).detDualEquiv.toLinearMap chargeMap := by
  ext i j
  rw [SkewExchangeMatrix.neg_matrix, Matrix.neg_apply, exchangeMatrix_eq_chargeExchangeMatrix,
    chargeExchangeMatrix_apply, chargeExchangeMatrix_apply]
  simpa only [LinearEquiv.coe_coe, LinearMap.neg_apply] using
    congrArg (fun ℓ : (Fin 2 → ℤ) →ₗ[ℤ] ℤ ↦ ℓ (chargeMap (Pi.single j 1)))
      ((Pi.basisFun ℤ (Fin 2)).detDualEquiv_reindex_swap (chargeMap (Pi.single i 1))).symm

private theorem xPullback_eq_iff_columns (w v : Word B B) :
    w.xPullback k = v.xPullback k ↔ transportedColumns w = transportedColumns v := by
  obtain ⟨X, f, hsm, D, hD, _, hpre, _, _, A, Y, T, e, _, hint, hproj, hrat, _, _, _, hprim,
    hnef, hsq, hT, hbase, hker, _, _, _, _⟩ := exists_eleven_vertex_toric_presentation (fun _ ↦ 1)
  let S := Spec (CommRingCat.of ℂ)
  let : X.Over S := ⟨f⟩
  let : (Iso.refl D.subscheme).hom.IsOver S :=
    inferInstanceAs ((𝟙 D.subscheme : D.subscheme ⟶ D.subscheme).IsOver S)
  let A' := (Iso.refl D.subscheme).mapNodalCycleNumbering A
    (q := (Empty.elim : Empty → (D.subscheme ↘ S).smoothLocus))
  let b := Pi.basisFun ℤ (Fin 2)
  let hi := isIntegralLattice_intCast 2
  let hc := Fan.isComplete_projectiveSpace b hi
  let : Scheme.IsRationalOver (X ↘ S) := hrat
  let : Module.Free ℤ (Additive (LineBundleClass X)) := X.free_picard_of_isRationalOver ℂ
  let : Module.Finite ℤ (Additive (LineBundleClass X)) := X.finite_picard_of_isRationalOver ℂ
  let ePic := (Module.finBasis ℤ (Additive (LineBundleClass X))).equivFun.symm
  let μ := ((Chow.intersectionBilinForm ℂ X).isometryEquivOfCompLinearEquiv ePic).symm
  obtain ⟨b', ⟨Q, c, g, href⟩, hframe, ⟨hfan, hrays⟩⟩ :=
    exists_marked_reference_fiber_of_ordered_towers
      (Fan.isRegular_projectiveSpace b hi) hc planeCenterRay (fun _ ↦ 1)
      hT e hbase hker hD A' μ
  let chargeOfRays (p : Σ Φ : Fan (AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin 2)),
      Fin 11 → Φ.Ray) := Fan.rayChargeMap p.2
  have hrayData : (⟨Q.fan, Q.rays⟩ : Σ Φ : Fan _, Fin 11 → Φ.Ray) =
      ⟨Fan.projectiveSpace b hi, planeCenterRay⟩ :=
    Sigma.ext hfan
      ((eqRec_heq (φ := fun Φ : Fan _ ↦ Fin 11 → Φ.Ray) hfan Q.rays).symm.trans
        (heq_of_eq hrays))
  have hcharge : Fan.rayChargeMap Q.rays = chargeMap :=
    (congrArg chargeOfRays hrayData).trans rayChargeMap_planeCenterRay
  let M := MarkedSurface.ofBoundary D A' μ g
  have hM : M.pair.hom.left.ker = D := MarkedSurface.ofBoundary_ker ..
  have hcls : (LineBundleClass.mk M.isEffectiveCartier_boundaryIdeal.toInvertibleSheaf)⁻¹ =
      (LineBundleClass.mk hD.toInvertibleSheaf)⁻¹ := by
    exact congrArg Inv.inv (LineBundleClass.mk_toInvertibleSheaf_congr _ _ hM)
  have criterion {E : SkewExchangeMatrix (Fin 11)}
      (hE : E.matrix = chargeExchangeMatrix b'.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
      (hK : E.matrix.mulVecLin.ker = K) (p q : Word E E) :
      p.xPullback k = q.xPullback k ↔ transportedColumns p = transportedColumns q := by
    let β := exchangeKernelBasis.map (LinearEquiv.ofEq _ _ hK.symm)
    simpa only [transportedColumns, funext_iff, β, Module.Basis.map_apply,
      LinearEquiv.coe_ofEq_apply, coe_exchangeKernelBasis_apply] using
      Q.xPullback_eq_iff_exponentEquiv_eq_on_basis_of_squarefree href hE
        (by rw [hcls]; exact hprim) (by rw [hcls]; exact hnef)
        (by rw [hcls]; exact hsq) squarefree_one k p q β
  rcases hframe with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact criterion (by rw [hcharge]; exact exchangeMatrix_eq_chargeExchangeMatrix) rfl w v
  · apply xPullback_eq_iff_columns_of_neg k _ w v
    exact criterion (by rw [hcharge]; exact neg_exchangeMatrix_eq_chargeExchangeMatrix)
      (by ext x; simp [SkewExchangeMatrix.neg_matrix, LinearMap.mem_ker])

/-- Two signed eleven-vertex loops over a characteristic-zero field have the same X pullback
exactly when their integral exchange-kernel actions agree. -/
theorem xPullback_eq_iff_exchangeKernelEquiv_eq (w v : Word B B) :
    w.xPullback k = v.xPullback k ↔ w.exchangeKernelEquiv = v.exchangeKernelEquiv := by
  refine ⟨Path.exchangeKernelEquiv_eq_of_xPullback_eq k, fun h ↦ ?_⟩
  apply (xPullback_eq_iff_columns k w v).mpr
  funext j
  simpa only [transportedColumns, Path.coe_exchangeKernelEquiv_apply,
    coe_exchangeKernelBasis_apply] using
    congrArg (fun e : K ≃ₗ[ℤ] K ↦ (e (exchangeKernelBasis j) : Fin 11 → ℤ)) h

/-- The integral exchange-kernel action of the eleven-vertex signed cluster modular group
over a characteristic-zero field is faithful. -/
theorem exchangeKernelAction_injective :
    Function.Injective (exchangeKernelAction k B) := by
  intro x y h
  obtain ⟨w, hw⟩ := signedClusterModularGroupMap_surjective k B x.unop
  obtain ⟨v, hv⟩ := signedClusterModularGroupMap_surjective k B y.unop
  rw [← op_unop x, ← op_unop y, ← hw, ← hv] at h ⊢
  rw [exchangeKernelAction_op_loop, exchangeKernelAction_op_loop] at h
  exact congrArg op ((signedClusterModularGroupMap_eq_iff k B w v).mpr
    ((xPullback_eq_iff_exchangeKernelEquiv_eq k w.asHom v.asHom).mpr h))

/-- In the eleven-vertex seed, the complete integer invariant detects equality of X pullbacks
over every characteristic-zero field. The columns already distinguish the pullbacks. -/
theorem xPullback_eq_iff_signedLoopInvariants_eq (w v : Word B B) :
    w.xPullback k = v.xPullback k ↔
      w.signedLoopInvariants exchangeKernelBasisVectors boundaryOrders (boundaryOrders 0) =
        v.signedLoopInvariants exchangeKernelBasisVectors boundaryOrders (boundaryOrders 0) := by
  constructor
  · intro h
    simpa only [coe_exchangeKernelBasis_apply] using
      Path.signedLoopInvariants_eq_of_xPullback_eq exchangeMatrix_matrix_ne_zero h
        exchangeKernelBasis boundaryOrders (boundaryOrders 0)
  · intro h
    apply (xPullback_eq_iff_columns k w v).mpr
    unfold transportedColumns
    simpa only [Path.signedLoopInvariants_kernelColumns, Matrix.of_apply] using
      congrArg (fun t : SignedLoopInvariants (Fin 11) (Fin 9) 1 ↦
        fun j i ↦ t.kernelColumns i j) h

/-- Decide equality of independent X pullbacks by comparing the nine transported
integral Casimir basis vectors. -/
def decidableXPullbackEq (w v : Word B B) : Decidable (w.xPullback k = v.xPullback k) :=
  decidable_of_iff (transportedColumns w = transportedColumns v)
    (xPullback_eq_iff_columns k w v).symm

end QPainleve.ElevenVertex
