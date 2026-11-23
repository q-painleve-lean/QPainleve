/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.BoundaryRestriction
public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.Period

import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# The period character of a surface with nodal boundary

A surface class orthogonal to the components of a nodal rational boundary restricts to
a class of multidegree zero. Its period is the oriented product of the gluing ratios of
that restriction. Divisors disjoint from the boundary have trivial period. See Gross,
Hacking and Keel, [*Moduli of surfaces with an anti-canonical cycle*, §2](https://arxiv.org/abs/1211.6367v5).
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

universe u v w

variable {k : Type u} [Field k] [IsAlgClosed k]
  {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  (hD : D.IsEffectiveCartier)

local notation "ν[" I "]" => IdealSheafData.blowupToBase (Scheme.singularLocus k
  (IdealSheafData.subscheme I))
variable (hgenus : ∀ v : irreducibleComponents (D.subscheme.singularLocus k).blowup,
    (D.subscheme.blowupComponent v).toScheme.genus k = 0)
variable {α : Type v} (p : α → (D.subscheme ↘ Spec (.of k)).smoothLocus)
  {n : ℕ} [NeZero n] (e : ZMod n ≃ (D.subscheme.dualGraph p).Edge)
  (o : (D.subscheme.dualGraph p).Edge → Equiv.Perm (Fin 2))
  (vtx : ZMod n ≃ (D.subscheme.dualGraph p).Vertex)
  (h : ∀ i b, (D.subscheme.dualGraph p).endpoint (e i) (o (e i) b) =
    vtx ((DualGraph.cycle n).endpoint i b))

/-- Restrict a boundary-orthogonal surface class to the boundary. Its pullback to
the normalization is trivial by the multidegree calculation. -/
def boundaryRestrictionHom :
    Multiplicative (D.boundaryOrthogonal k) →* (LineBundleClass.pullbackHom (ν[D])).ker :=
  ((LineBundleClass.pullbackHom D.subschemeι).comp
    (D.boundaryOrthogonal k).subtype.toAddMonoidHom.toMultiplicativeLeft).codRestrict _ fun a ↦ by
      simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, pullbackHom_apply,
        AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
        Submodule.subtype_apply, pullback_comp] using
        (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal hgenus _).mpr
          a.toAdd.property

/-- Forgetting the normalization condition gives ordinary Picard restriction. -/
@[simp]
theorem coe_boundaryRestrictionHom (a : Multiplicative (D.boundaryOrthogonal k)) :
    (hD.boundaryRestrictionHom hgenus a).val = pullback D.subschemeι a.toAdd.val.toMul := by
  simp only [boundaryRestrictionHom, MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    pullbackHom_apply, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply]

/-- The period character on the boundary orthogonal lattice of a surface with
an oriented nodal cycle of rational curves. -/
def boundaryPeriod : Multiplicative (D.boundaryOrthogonal k) →* kˣ :=
  (D.subscheme.nodalPicardCycleMulEquiv p e o vtx h).toMonoidHom.comp
    (hD.boundaryRestrictionHom hgenus)

/-- The value of the period character is the period of the restricted class. -/
theorem boundaryPeriod_apply (a : Multiplicative (D.boundaryOrthogonal k)) :
    hD.boundaryPeriod hgenus p e o vtx h a =
      D.subscheme.nodalPicardCycleMulEquiv p e o vtx h (hD.boundaryRestrictionHom hgenus a) :=
  (rfl)

/-- A boundary-orthogonal class has period one exactly when its restriction to
the boundary is the trivial line bundle. -/
theorem boundaryPeriod_eq_one_iff (a : Multiplicative (D.boundaryOrthogonal k)) :
    hD.boundaryPeriod hgenus p e o vtx h a = 1 ↔ pullback D.subschemeι a.toAdd.val.toMul = 1 := by
  rw [boundaryPeriod_apply, MulEquiv.map_eq_one_iff, Subtype.ext_iff,
    coe_boundaryRestrictionHom, Subgroup.coe_one]

omit [IsIntegral X] in
private theorem pullback_effectiveCartierClass_eq_one_of_disjoint {C : X.IdealSheafData}
    (hC : C.IsEffectiveCartier) (hdisj : Disjoint (D.support : Set X) C.support) :
    pullback D.subschemeι (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ = 1 := by
  have htop : C.comap D.subschemeι = ⊤ := by
    rw [C.comap_eq_top_iff, eq_top_iff]
    intro x _
    rw [Scheme.Hom.mem_preimage, ← SetLike.mem_coe, Closeds.coe_compl, Set.mem_compl_iff]
    exact fun hx ↦ Set.disjoint_left.mp hdisj (D.range_subschemeι.le (Set.mem_range_self x)) hx
  rw [pullback_inv, hC.pullback_mk_toInvertibleSheaf_eq_one_of_comap_eq_top _ htop, inv_one]

include hD hgenus in
/-- The class of an effective Cartier divisor disjoint from the boundary lies in the
boundary orthogonal. In particular this applies to internal prime curves. -/
theorem effectiveCartierClass_mem_orthogonal_of_disjoint {C : X.IdealSheafData}
    (hC : C.IsEffectiveCartier) (hdisj : Disjoint (D.support : Set X) C.support) :
    Additive.ofMul (LineBundleClass.mk hC.toInvertibleSheaf)⁻¹ ∈ D.boundaryOrthogonal k := by
  apply (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal hgenus _).mp
  rw [toMul_ofMul, ← pullback_comp, pullback_effectiveCartierClass_eq_one_of_disjoint hC hdisj,
    pullback_one]

/-- The period of an effective Cartier divisor disjoint from the boundary is one.
This gives the period obstruction for an internal curve of square `-2`. -/
theorem boundaryPeriod_effectiveCartierClass_eq_one_of_disjoint {C : X.IdealSheafData}
    (hC : C.IsEffectiveCartier) (hdisj : Disjoint (D.support : Set X) C.support) :
    hD.boundaryPeriod hgenus p e o vtx h
        (Multiplicative.ofAdd ⟨_, hD.effectiveCartierClass_mem_orthogonal_of_disjoint
          hgenus hC hdisj⟩) = 1 := by
  rw [boundaryPeriod_eq_one_iff, toAdd_ofAdd, Subtype.coe_mk, toMul_ofMul]
  exact pullback_effectiveCartierClass_eq_one_of_disjoint hC hdisj

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {E : Y.IdealSheafData} [PrestableFamily (E.subscheme ↘ Spec (.of k))]
  (hE : E.IsEffectiveCartier)
  (hgenusE : ∀ v : irreducibleComponents (E.subscheme.singularLocus k).blowup,
    (E.subscheme.blowupComponent v).toScheme.genus k = 0)

section Pullback

variable (f : X ⟶ Y) (g : D.subscheme ≅ E.subscheme) [g.hom.IsOver (Spec (.of k))]
  (hcomm : D.subschemeι ≫ f = g.hom ≫ E.subschemeι)

/-- In a commutative square with an isomorphism of the rational nodal boundaries,
pullback sends classes orthogonal to the target boundary into the source boundary
orthogonal. -/
def boundaryOrthogonalPullback :
    E.boundaryOrthogonal k →ₗ[ℤ] D.boundaryOrthogonal k :=
  (((pullbackHom f).toAdditive.toIntLinearMap).comp (E.boundaryOrthogonal k).subtype).codRestrict
    (D.boundaryOrthogonal k) fun b ↦ by
      apply (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal hgenus _).mp
      have hb := (g.nodalPicardKernelPullback (k := k)
        (hE.boundaryRestrictionHom hgenusE (Multiplicative.ofAdd b))).property
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, AddMonoidHom.coe_toIntLinearMap,
        MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul, pullbackHom_apply]
      rw [← pullback_comp (ν[D]) D.subschemeι, pullback_comp D.subschemeι f, hcomm,
        ← pullback_comp g.hom E.subschemeι]
      simpa only [MonoidHom.mem_ker, pullbackHom_apply, Iso.coe_nodalPicardKernelPullback,
        coe_boundaryRestrictionHom, toAdd_ofAdd] using hb

/-- The induced map on boundary orthogonals is ordinary Picard pullback. -/
@[simp]
theorem coe_boundaryOrthogonalPullback (b : E.boundaryOrthogonal k) :
    (hD.boundaryOrthogonalPullback hgenus hE hgenusE f g hcomm b).val.toMul =
      pullback f b.val.toMul := by
  simp only [boundaryOrthogonalPullback, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul, pullbackHom_apply]

end Pullback

variable {β : Type w} (pE : β → (E.subscheme ↘ Spec (.of k)).smoothLocus)
  {m : ℕ} [NeZero m] (eE : ZMod m ≃ (E.subscheme.dualGraph pE).Edge)
  (oE : (E.subscheme.dualGraph pE).Edge → Equiv.Perm (Fin 2))
  (vtxE : ZMod m ≃ (E.subscheme.dualGraph pE).Vertex)
  (hEcycle : ∀ i b, (E.subscheme.dualGraph pE).endpoint (eE i) (oE (eE i) b) =
    vtxE ((DualGraph.cycle m).endpoint i b))

/-- The boundary period commutes with pullback along a commutative square whose boundary
map is an isomorphism. It is inverted if the boundary map reverses every branch order. -/
theorem boundaryPeriod_pullback_of_boundaryIso
    (f : X ⟶ Y) (g : D.subscheme ≅ E.subscheme) [g.hom.IsOver (Spec (.of k))]
    (hcomm : D.subschemeι ≫ f = g.hom ≫ E.subschemeι)
    (b : E.boundaryOrthogonal k)
    (swap : Bool) (horder : ∀ (z : (D.subscheme.singularLocus k).subscheme) (i : Fin 2),
      (g.branchSchemeIso (R := k)).hom (D.subscheme.branchOrderOfDualGraph p o z i).val =
        (E.subscheme.branchOrderOfDualGraph pE oE ((g.singularLocusIso (R := k)).hom z)
          (if swap then i.rev else i)).val) :
    hD.boundaryPeriod hgenus p e o vtx h
        (Multiplicative.ofAdd (hD.boundaryOrthogonalPullback hgenus hE hgenusE f g hcomm b)) =
      if swap then (hE.boundaryPeriod hgenusE pE eE oE vtxE hEcycle (Multiplicative.ofAdd b))⁻¹
      else hE.boundaryPeriod hgenusE pE eE oE vtxE hEcycle (Multiplicative.ofAdd b) := by
  have hres : hD.boundaryRestrictionHom hgenus
        (Multiplicative.ofAdd (hD.boundaryOrthogonalPullback hgenus hE hgenusE f g hcomm b)) =
      g.nodalPicardKernelPullback (k := k)
        (hE.boundaryRestrictionHom hgenusE (Multiplicative.ofAdd b)) := by
    apply Subtype.ext
    simp only [coe_boundaryRestrictionHom, Iso.coe_nodalPicardKernelPullback,
      toAdd_ofAdd, coe_boundaryOrthogonalPullback, pullback_comp, hcomm]
  simp only [boundaryPeriod_apply, hres]
  exact g.nodalPicardCycleMulEquiv_pullback p pE e eE o oE vtx vtxE h hEcycle _ swap horder

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
