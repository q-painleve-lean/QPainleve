/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.CycleProduct
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Naturality
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Picard

/-!
# The Picard period of an oriented nodal cycle

The normalization kernel in the Picard group is isomorphic to the units of the
ground field by the oriented product of branch gluing ratios. Pullback along
an isomorphism preserving the branch orders preserves the period, and reversing
all the orders inverts it. See Gross, Hacking and Keel,
[*Moduli of surfaces with an anti-canonical cycle*, Lemma 2.1](https://arxiv.org/abs/1211.6367v5).
-/

public noncomputable section

open CategoryTheory MonoidalCategory TauCeti TauCeti.AlgebraicGeometry
open AlgebraicGeometry Scheme.Modules

universe u v w

local notation "ν[" k ", " X "]" => Scheme.IdealSheafData.blowupToBase (Scheme.singularLocus k X)
local notation "ι[" k ", " X "]" => Scheme.IdealSheafData.subschemeι (Scheme.singularLocus k X)
local notation "conductorSq[" k ", " X "]" =>
  IsPullback.toCommSq (IsPullback.flip (Scheme.isPullback_branchScheme k X))

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : Scheme.{u}) [X.Over (Spec (.of k))] [PrestableFamily (X ↘ Spec (.of k))]
variable {ι : Type v} (p : ι → (X ↘ Spec (.of k)).smoothLocus)
variable {n : ℕ} [NeZero n] (e : ZMod n ≃ (X.dualGraph p).Edge)
variable (o : (X.dualGraph p).Edge → Equiv.Perm (Fin 2))
variable (vtx : ZMod n ≃ (X.dualGraph p).Vertex)
variable (h : ∀ i b, (X.dualGraph p).endpoint (e i) (o (e i) b) =
  vtx ((DualGraph.cycle n).endpoint i b))

local notation "nodal" => PrestableFamily.atWorstNodalOfRelativeDimensionOne

/-- The period isomorphism of an oriented nodal cycle. Its source consists of the line
bundle classes trivial on the normalization. For rational components this is the
multidegree-zero Picard group. -/
def nodalPicardCycleMulEquiv : (LineBundleClass.pullbackHom (ν[k, X])).ker ≃* kˣ :=
  (X.nodalPicardKernelMulEquiv nodal).trans (X.nodalConductorCycleProductEquiv p e o vtx h)

/-- Calculate the period using any trivializations on the normalization and singular
subscheme. The contribution of each node is the branch-one value divided by branch zero. -/
theorem nodalPicardCycleMulEquiv_apply
    (a : (LineBundleClass.pullbackHom (ν[k, X])).ker) (L : InvertibleSheaf X)
    (t : (pullback (ν[k, X])).obj L.obj ≅ 𝟙_ _)
    (d : (pullback (ι[k, X])).obj L.obj ≅ 𝟙_ _) (hL : LineBundleClass.mk L = a.val) :
    X.nodalPicardCycleMulEquiv p e o vtx h a =
      X.nodalConductorCycleProduct p e o ((conductorSq[k, X]).lineGluingUnit t d) := by
  rw [nodalPicardCycleMulEquiv, MulEquiv.trans_apply,
    nodalPicardKernelMulEquiv_apply nodal a L t d hL, nodalConductorCycleProductEquiv_mk]

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Iso

section Pullback

variable {k : Type u} [CommRing k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] (f : X ≅ Y) [f.hom.IsOver (Spec (.of k))]
variable [Flat (X ↘ Spec (.of k))] [LocallyOfFinitePresentation (X ↘ Spec (.of k))]
  [PureRelativeDimension 1 (X ↘ Spec (.of k))]
  [Flat (Y ↘ Spec (.of k))] [LocallyOfFinitePresentation (Y ↘ Spec (.of k))]
  [PureRelativeDimension 1 (Y ↘ Spec (.of k))]

/-- Pullback along an isomorphism of curves preserves the Picard subgroup trivialized
by the blowup of the singular locus. -/
def nodalPicardKernelPullback :
    (LineBundleClass.pullbackHom (ν[k, Y])).ker →*
      (LineBundleClass.pullbackHom (ν[k, X])).ker :=
  ((LineBundleClass.pullbackHom f.hom).comp (Subgroup.subtype _)).codRestrict _ fun a ↦ by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply,
      LineBundleClass.pullbackHom_apply, LineBundleClass.pullbackHom_apply,
      LineBundleClass.pullback_comp, ← f.singularLocusBlowupIso_hom_blowupToBase (R := k),
      ← LineBundleClass.pullback_comp]
    have ha : LineBundleClass.pullback (ν[k, Y]) a.val = 1 := by
      simpa only [LineBundleClass.pullbackHom_apply] using MonoidHom.mem_ker.mp a.property
    rw [ha, LineBundleClass.pullback_one]

/-- The underlying Picard class is the ordinary pullback. -/
@[simp]
theorem coe_nodalPicardKernelPullback (a : (LineBundleClass.pullbackHom (ν[k, Y])).ker) :
    (f.nodalPicardKernelPullback (k := k) a).val = LineBundleClass.pullback f.hom a.val := by
  simp only [nodalPicardKernelPullback, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply, LineBundleClass.pullbackHom_apply]

end Pullback

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}}
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] (f : X ≅ Y) [f.hom.IsOver (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))] [PrestableFamily (Y ↘ Spec (.of k))]
variable {α : Type v} {β : Type w}
  (pX : α → (X ↘ Spec (.of k)).smoothLocus) (pY : β → (Y ↘ Spec (.of k)).smoothLocus)
variable {n m : ℕ} [NeZero n] [NeZero m]
  (eX : ZMod n ≃ (X.dualGraph pX).Edge) (eY : ZMod m ≃ (Y.dualGraph pY).Edge)
  (oX : (X.dualGraph pX).Edge → Equiv.Perm (Fin 2))
  (oY : (Y.dualGraph pY).Edge → Equiv.Perm (Fin 2))
  (vX : ZMod n ≃ (X.dualGraph pX).Vertex) (vY : ZMod m ≃ (Y.dualGraph pY).Vertex)
  (hX : ∀ i b, (X.dualGraph pX).endpoint (eX i) (oX (eX i) b) =
    vX ((DualGraph.cycle n).endpoint i b))
  (hY : ∀ i b, (Y.dualGraph pY).endpoint (eY i) (oY (eY i) b) =
    vY ((DualGraph.cycle m).endpoint i b))

/-- Pulling back a period class preserves its period when the ordered branches agree at
every node and inverts it when their orders are all reversed. The comparison is independent
of the starting nodes of the two cyclic numberings. -/
theorem nodalPicardCycleMulEquiv_pullback
    (a : (LineBundleClass.pullbackHom (ν[k, Y])).ker) (swap : Bool)
    (horder : ∀ (z : (X.singularLocus k).subscheme) (i : Fin 2),
      (f.branchSchemeIso (R := k)).hom (X.branchOrderOfDualGraph pX oX z i).val =
        (Y.branchOrderOfDualGraph pY oY ((f.singularLocusIso (R := k)).hom z)
          (if swap then i.rev else i)).val) :
    X.nodalPicardCycleMulEquiv pX eX oX vX hX (f.nodalPicardKernelPullback (k := k) a) =
      if swap then (Y.nodalPicardCycleMulEquiv pY eY oY vY hY a)⁻¹
      else Y.nodalPicardCycleMulEquiv pY eY oY vY hY a := by
  have hn := PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := Y ↘ Spec (.of k))
  have ha := a.property
  have hd := Y.pullback_singularLocus_subschemeι_eq_one hn a.val
  obtain ⟨L, hL⟩ := LineBundleClass.mk_surjective a.val
  rw [← hL, MonoidHom.mem_ker, LineBundleClass.pullbackHom_apply,
    LineBundleClass.pullback_mk, LineBundleClass.mk_eq_one_iff] at ha
  rw [← hL, LineBundleClass.pullback_mk, LineBundleClass.mk_eq_one_iff] at hd
  obtain ⟨t⟩ := ha
  obtain ⟨d⟩ := hd
  let nt := CommSq.mk (f.singularLocusBlowupIso_hom_blowupToBase (R := k)).symm
  let nd := CommSq.mk (f.singularLocusIso_hom_subschemeι (R := k)).symm
  have hL' : LineBundleClass.mk ((InvertibleSheaf.pullback f.hom).obj L) =
      (f.nodalPicardKernelPullback (k := k) a).val := by
    rw [← LineBundleClass.pullback_mk, coe_nodalPicardKernelPullback, hL]
  rw [X.nodalPicardCycleMulEquiv_apply _ _ _ _ _ _ _
    (nt.pullbackTrivialization t) (nd.pullbackTrivialization d) hL',
    Y.nodalPicardCycleMulEquiv_apply _ _ _ _ _ _ L t d hL,
    X.nodalConductorCycleProduct_eq_finprod, Y.nodalConductorCycleProduct_eq_finprod]
  exact f.finprod_branchRatioHom_lineGluingUnit_pullback
    PrestableFamily.atWorstNodalOfRelativeDimensionOne hn
    (X.branchOrderOfDualGraph pX oX) (Y.branchOrderOfDualGraph pY oY) t d swap horder

end CategoryTheory.Iso
