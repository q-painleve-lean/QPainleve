/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Relations
public import QPainleve.SignedClusterModularGroup.Realization.Presentation
public import QPainleve.SignedClusterModularGroup.Realization.Tropical

import QPainleve.SignedClusterModularGroup.Realization.NodalFiber
import QPainleve.SignedClusterModularGroup.Realization.Presentation.Boundary

/-!
# Conjugation of the integer invariants of signed cluster loops

A connecting realization transports the full table of boundary orders by its
forward boundary permutation. This identifies the boundary search of a conjugated
loop in terms of the two geometric permutations. The Casimir matrix changes by
conjugation in the respective exchange-kernel bases and the inversion sign is preserved.
The conjugate word represents the conjugation of point maps in
`Cluster.signedClusterModularGroupCongr_map`. Order transport uses
`FiberRealization.rayBoundaryOrders_tropical`.
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Module Quiver
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric
open Scheme

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "Centers[" r "]" => Over.mk (structureMap ℂ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "src(" C "," x ")" =>
  x ≫ Scheme.PartialMap.domainSource (X := Centers[_]) (Y := Centers[_]) C
local notation "dst(" C "," x ")" =>
  x ≫ Scheme.PartialMap.domainTarget (X := Centers[_]) (Y := Centers[_]) C
local notation "cartier(" M ")" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "χ[" c "]" => pointsEquiv ℂ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "trop[" w "]" =>
  DFunLike.coe (F := Equiv.Perm (Fin _ → ℤ))
    (CategoryTheory.Functor.map (Paths.lift (tropicalPrefunctor (A := ℤ) (Fin _))) w)

variable {r n : ℕ} [NeZero n] {E E' : SkewExchangeMatrix (Fin r)}
  {N N' V V' : Type} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup V]
  [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {b : Basis (Fin 2) ℤ N} {b' : Basis (Fin 2) ℤ N'}
  {L L' γ γ' : Type} [AddCommGroup L] [AddCommGroup L']
  {H : LinearMap.BilinForm ℤ L} {H' : LinearMap.BilinForm ℤ L'}
  {M : Point Centers[r] → MarkedSurface ℂ n H XTor[r]}
  {M' : Point Centers[r] → MarkedSurface ℂ n H' XTor[r]}
  {C D : Centers[r].left.PartialMap Centers[r].left}
  [IsDominant C.hom] [C.IsOver Centers[r].hom Centers[r].hom]
  [IsDominant D.hom] [D.IsOver Centers[r].hom Centers[r].hom]
  {w : Word E E'} {v : Word E E}

local instance instNonemptyConjugationCones (Q : CompleteToricPresentation i b r L γ) :
    Nonempty Q.fan.cones := Q.complete.nonempty_cones
local instance instNeZeroConjugationBoundaryLength (Q : CompleteToricPresentation i b r L γ) :
    NeZero Q.length := Q.neZero
local instance instPrestableConjugationBoundary (Q : CompleteToricPresentation i b r L γ) :
    PrestableFamily ((Q.fan.boundaryIdeal Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "Fiber[" basis "," Q "," M "," c "]" =>
  ContractedToricFiber basis (CompleteToricPresentation.rays Q)
    (CompleteToricPresentation.regular Q) (CompleteToricPresentation.cycle Q)
    (CompleteToricPresentation.origin Q)
    (CompleteToricPresentation.inclusion Q) χ[c] (M c)
local notation "label[" R "]" =>
  (Equiv.trans (RingEquiv.toEquiv (ZMod.finEquiv n))
    (Equiv.trans (GeometricRealization.boundaryPerm R)
      (Equiv.symm (RingEquiv.toEquiv (ZMod.finEquiv n)))))

/-- A connecting realization transports the order vectors of all the numbered
boundary components. Each table can be taken from any reference nodal contraction
of its presentation. The result is independent of the reference centers. -/
theorem tropical_boundaryOrders_of_nodal_models
    (R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r]) M M' C (w.xRationalMap ℂ))
    (Q : CompleteToricPresentation i b r L γ)
    (Q' : CompleteToricPresentation i' b' r L' γ')
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    {c : Point Centers[r]} {c' : Point Centers[r]}
    {p : Fiber[b,Q,M,c]} {p' : Fiber[b',Q',M',c']}
    (hp : p.IsNodalContraction) (hp' : p'.IsNodalContraction)
    (x : CenterPoint (U := Centers[r]) (V := Centers[r]) C)
    (hx : Q.HasNodalModel (src(C,x)) (M (src(C,x))))
    (hx' : Q'.HasNodalModel (dst(C,x)) (M' (dst(C,x)))) (j : Fin n) :
    trop[w] (p.numberedBoundaryOrders hp.cartier j) =
      p'.numberedBoundaryOrders hp'.cartier (label[R] j) := by
  obtain ⟨q, hq⟩ := hx.exists_isNodalContraction (cartier(M (src(C,x))))
  obtain ⟨q', hq'⟩ := hx'.exists_isNodalContraction (cartier(M' (dst(C,x))))
  have h := (R.fiber x).rayBoundaryOrders_tropical (p := q) (q := q')
    hq.cartier hq'.cartier Q.complete hE ((ZMod.finEquiv n).toEquiv j)
  rw [Q.numberedBoundaryRays_eq_of_nodalContractions hq hp,
    Q'.numberedBoundaryRays_eq_of_nodalContractions hq' hp'] at h
  simpa only [ContractedToricFiber.numberedBoundaryOrders_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, R.boundaryPerm_def] using h.symm

/-- Conjugation by a realized connecting word preserves the inversion sign,
conjugates the Casimir matrix in the chosen integral bases, and computes the
new boundary label from the two signs and forward images of zero. The two
order tables come from arbitrary reference nodal contractions. -/
theorem signedLoopInvariants_reverse_comp_comp
    (R : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r]) M M' C (w.xRationalMap ℂ))
    (A : GeometricRealization (T₀ := Centers[r]) (T₁ := Centers[r]) M M D (v.xRationalMap ℂ))
    (Q : CompleteToricPresentation i b r L γ)
    (Q' : CompleteToricPresentation i' b' r L' γ')
    (hE : E.matrix = chargeExchangeMatrix b.detDualEquiv.toLinearMap (Fan.rayChargeMap Q.rays))
    (hindex : (Fan.rayChargeMap Q'.rays).range.toAddSubgroup.index ≠ 0)
    {c : Point Centers[r]} {c' : Point Centers[r]}
    {p : Fiber[b,Q,M,c]} {p' : Fiber[b',Q',M',c']}
    (hp : p.IsNodalContraction) (hp' : p'.IsNodalContraction)
    (x : CenterPoint (U := Centers[r]) (V := Centers[r]) C)
    (hx : Q.HasNodalModel (src(C,x)) (M (src(C,x))))
    (hx' : Q'.HasNodalModel (dst(C,x)) (M' (dst(C,x))))
    (y : CenterPoint (U := Centers[r]) (V := Centers[r]) D)
    (hy : Q.HasNodalModel (src(D,y)) (M (src(D,y))))
    (hy' : Q.HasNodalModel (dst(D,y)) (M (dst(D,y))))
    {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (β : Basis κ ℤ E.matrix.mulVecLin.ker) (β' : Basis κ' ℤ E'.matrix.mulVecLin.ker) :
    let u := (w.reverse.comp v).comp w
    let o := p.numberedBoundaryOrders hp.cartier
    let o' := p'.numberedBoundaryOrders hp'.cartier
    (u.signedLoopInvariants (fun k ↦ (β' k : Fin r → ℤ)) o' (o' 0)).sign =
      (v.signedLoopInvariants (fun k ↦ (β k : Fin r → ℤ)) o (o 0)).sign ∧
    LinearMap.toMatrix β' β' u.exchangeKernelEquiv.toLinearMap =
      LinearMap.toMatrix β β' w.exchangeKernelEquiv.symm.toLinearMap *
        LinearMap.toMatrix β β v.exchangeKernelEquiv.toLinearMap *
        LinearMap.toMatrix β' β w.exchangeKernelEquiv.toLinearMap ∧
    ∀ j : Fin n, u.tropicalBoundaryLabel o' (o' j) =
      some ((ZMod.finEquiv n).toEquiv.symm (A.orientation •
        ((ZMod.finEquiv n).toEquiv j - R.boundaryPerm 0) +
          R.orientation • A.boundaryPerm 0 + R.boundaryPerm 0)) := by
  have hinj := p'.numberedBoundaryOrders_injective hp'.cartier hindex
  refine ⟨?_, w.toMatrix_exchangeKernelEquiv_reverse_comp_comp v β β', fun j ↦ ?_⟩
  · simpa only [Path.signedLoopInvariants_sign] using
      w.neg_one_pow_inversionCount_reverse_comp_comp v
  · rw [w.tropicalBoundaryLabel_reverse_comp_comp v hinj label[R] label[A]
      (R.tropical_boundaryOrders_of_nodal_models Q Q' hE hp hp' x hx hx')
      (A.tropical_boundaryOrders_of_nodal_models Q Q hE hp hp y hy hy') j]
    simp only [Equiv.trans_apply, Equiv.symm_trans, Equiv.symm_symm, Equiv.apply_symm_apply,
      R.boundaryPerm_def, A.boundaryPerm_def, R.orientation_def, A.orientation_def]
    refine congrArg (fun l ↦ some ((ZMod.finEquiv n).toEquiv.symm l)) ?_
    simpa only [map_mul, map_inv, Equiv.Perm.mul_apply, Equiv.Perm.inv_def] using
      cycleVertexPerm_mul_mul_inv_apply R.boundaryAction A.boundaryAction
        ((ZMod.finEquiv n).toEquiv j)

end QPainleve.SignedClusterModularGroup.GeometricRealization
