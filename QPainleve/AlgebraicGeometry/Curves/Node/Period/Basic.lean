/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.CycleProduct
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Picard
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Naturality

/-!
# Picard periods of oriented nodal cycles

The kernel of Picard pullback to the normalization is isomorphic to the units of the
base field by taking the product of the branch gluing ratios. An isomorphism of curves
preserves or inverts the period according to its action on the ordered branches.
The ordering retains both branches of a self-node and both nodes of a two-component cycle.

See [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Lemma 2.1](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory TauCeti TauCeti.AlgebraicGeometry
open Scheme.Modules

universe u v v'

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [PrestableFamily (X ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus}
  {n : ℕ} [NeZero n]

local notation "ν[" C "]" => IdealSheafData.blowupToBase (singularLocus k C)
local notation "ι[" C "]" => IdealSheafData.subschemeι (singularLocus k C)
local notation "P[" C "]" => MonoidHom.ker (LineBundleClass.pullbackHom (ν[C]))
local notation "nodal" => PrestableFamily.atWorstNodalOfRelativeDimensionOne

variable {e : ZMod n ≃ (X.dualGraph p).Edge}
  {o : (X.dualGraph p).Edge → Equiv.Perm (Fin 2)}
  {w : ZMod n ≃ (X.dualGraph p).Vertex}
  (hw : ∀ i b, (X.dualGraph p).endpoint (e i) (o (e i) b) =
    w ((DualGraph.cycle n).endpoint i b))

/-- The period of a line bundle trivial on the normalization of an oriented nodal cycle,
as a multiplicative equivalence. For rational components this domain is the subgroup of
multidegree-zero line bundle classes. -/
def nodalPicardCycleMulEquiv : P[X] ≃* kˣ :=
  (nodalPicardKernelMulEquiv nodal).trans (X.nodalConductorCycleProductEquiv p e o w hw)

/-- Compute the period of a Picard class from any representative and any trivializations
of its pullbacks to the normalization and the singular subscheme. -/
theorem nodalPicardCycleMulEquiv_apply (a : P[X]) (L : InvertibleSheaf X)
    (t : (pullback (ν[X])).obj L.obj ≅ 𝟙_ _)
    (d : (pullback (ι[X])).obj L.obj ≅ 𝟙_ _) (hL : LineBundleClass.mk L = a.val) :
    nodalPicardCycleMulEquiv hw a =
      X.nodalConductorCycleProduct p e o
        ((X.isPullback_branchScheme k).flip.toCommSq.lineGluingUnit t d) := by
  rw [nodalPicardCycleMulEquiv, MulEquiv.trans_apply,
    nodalPicardKernelMulEquiv_apply nodal a L t d hL, nodalConductorCycleProductEquiv_mk]

/-- A change of initial component and node leaves the period unchanged. -/
theorem nodalPicardCycleMulEquiv_rotate (j : ZMod n) (a : P[X]) :
    nodalPicardCycleMulEquiv (e := (Equiv.addRight j).trans e) (o := o)
      (w := (Equiv.addRight j).trans w) (by
        intro i b
        simp only [Equiv.trans_apply, Equiv.coe_addRight, hw]
        apply congrArg w
        by_cases hb : b = 0 <;> simp [hb, add_right_comm]) a =
      nodalPicardCycleMulEquiv hw a := by
  obtain ⟨L, ⟨t⟩, ⟨d⟩, hL⟩ := exists_trivialized_representative_of_mem_nodalPicardKernel nodal a
  rw [nodalPicardCycleMulEquiv_apply _ a L t d hL, nodalPicardCycleMulEquiv_apply _ a L t d hL]
  exact X.nodalConductorCycleProduct_rotate p e o j _

/-- Reversing the cycle exchanges the two branches at every node and inverts the period. -/
theorem nodalPicardCycleMulEquiv_reverse (j : ZMod n) (a : P[X]) :
    nodalPicardCycleMulEquiv (e := (Equiv.subLeft j).trans e)
      (o := fun q ↦ (Equiv.swap 0 1).trans (o q))
      (w := (Equiv.subLeft (j + 1)).trans w) (by
        intro i b
        fin_cases b
        · simpa [DualGraph.cycle, sub_add_eq_add_sub] using hw (j - i) 1
        · have hj : j + 1 - (i + 1) = j - i := by abel
          simpa [DualGraph.cycle, hj] using hw (j - i) 0)
      a = (nodalPicardCycleMulEquiv hw a)⁻¹ := by
  obtain ⟨L, ⟨t⟩, ⟨d⟩, hL⟩ := exists_trivialized_representative_of_mem_nodalPicardKernel nodal a
  rw [nodalPicardCycleMulEquiv_apply _ a L t d hL, nodalPicardCycleMulEquiv_apply _ a L t d hL]
  exact X.nodalConductorCycleProduct_reverse p e o j _

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Iso

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [PrestableFamily (X ↘ Spec (.of k))]
  [Y.Over (Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]
  (f : X ≅ Y) [f.hom.IsOver (Spec (.of k))]

local notation "ν[" C "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus k C)
local notation "ι[" C "]" => Scheme.IdealSheafData.subschemeι (Scheme.singularLocus k C)
local notation "N[" C "]" => Scheme.IdealSheafData.subscheme (Scheme.singularLocus k C)
local notation "P[" C "]" => MonoidHom.ker (LineBundleClass.pullbackHom (ν[C]))
local notation "nodal" => PrestableFamily.atWorstNodalOfRelativeDimensionOne

variable [IsAlgClosed k] {n m : ℕ} [NeZero n] [NeZero m]
  {ιX : Type v} {ιY : Type v'}
  {pX : ιX → (X ↘ Spec (.of k)).smoothLocus}
  {pY : ιY → (Y ↘ Spec (.of k)).smoothLocus}
  {eX : ZMod n ≃ (X.dualGraph pX).Edge} {eY : ZMod m ≃ (Y.dualGraph pY).Edge}
  {oX : (X.dualGraph pX).Edge → Equiv.Perm (Fin 2)}
  {oY : (Y.dualGraph pY).Edge → Equiv.Perm (Fin 2)}
  {wX : ZMod n ≃ (X.dualGraph pX).Vertex} {wY : ZMod m ≃ (Y.dualGraph pY).Vertex}
  (hwX : ∀ i b, (X.dualGraph pX).endpoint (eX i) (oX (eX i) b) =
    wX ((DualGraph.cycle n).endpoint i b))
  (hwY : ∀ i b, (Y.dualGraph pY).endpoint (eY i) (oY (eY i) b) =
    wY ((DualGraph.cycle m).endpoint i b))

/-- The period of a pulled-back line bundle is preserved by an isomorphism respecting the
branch orders and inverted by an isomorphism reversing every branch order. -/
theorem nodalPicardCycleMulEquiv_pullback (swap : Bool)
    (horder : ∀ (z : N[X]) (b : Fin 2),
      (f.branchSchemeIso (R := k)).hom (X.branchOrderOfDualGraph pX oX z b).val =
        (Y.branchOrderOfDualGraph pY oY ((f.singularLocusIso (R := k)).hom z)
          (if swap then b.rev else b)).val)
    (a : P[Y]) :
    Scheme.nodalPicardCycleMulEquiv hwX
      ⟨LineBundleClass.pullback f.hom a.val,
        f.pullback_mem_ker_pullback_blowupToBase_singularLocus a⟩ =
      if swap then (Scheme.nodalPicardCycleMulEquiv hwY a)⁻¹
      else Scheme.nodalPicardCycleMulEquiv hwY a := by
  obtain ⟨L, ⟨t⟩, ⟨d⟩, hL⟩ :=
    Scheme.exists_trivialized_representative_of_mem_nodalPicardKernel nodal a
  let t' := (CommSq.mk (f.singularLocusBlowupIso_hom_blowupToBase (R := k)).symm)
    |>.pullbackTrivialization t
  let d' := (CommSq.mk (f.singularLocusIso_hom_subschemeι (R := k)).symm)
    |>.pullbackTrivialization d
  rw [Scheme.nodalPicardCycleMulEquiv_apply hwX _ ((InvertibleSheaf.pullback f.hom).obj L)
      t' d' (by rw [← LineBundleClass.pullback_mk, hL]),
    Scheme.nodalPicardCycleMulEquiv_apply hwY a L t d hL]
  simp only [Scheme.nodalConductorCycleProduct_eq_finprod]
  exact f.finprod_branchRatioHom_lineGluingUnit_pullback nodal nodal
    (X.branchOrderOfDualGraph pX oX) (Y.branchOrderOfDualGraph pY oY) t d swap horder

end CategoryTheory.Iso
