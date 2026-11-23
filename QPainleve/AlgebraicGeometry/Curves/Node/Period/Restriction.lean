/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.BoundaryRestriction
public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Basic
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback

/-!
# The boundary period character of a surface

Restriction takes a line bundle orthogonal to the boundary curves to a multidegree-zero
line bundle on the boundary. For an oriented nodal cycle the product of its gluing
ratios gives a character on the boundary orthogonal lattice. This is the period in
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*, §2](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open CategoryTheory TopologicalSpace TauCeti TauCeti.AlgebraicGeometry LineBundleClass

universe u v v'

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [X.IsProjectiveOver k] [IsIntegral X] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k))]
  (hD : D.IsEffectiveCartier)

local notation "C" => IdealSheafData.subscheme D
local notation "ν" => IdealSheafData.blowupToBase (Scheme.singularLocus k C)
local notation "PicZero" => MonoidHom.ker (pullbackHom ν)

local notation "K[" S "," J "]" =>
  Scheme.IdealSheafData.boundaryOrthogonal (X := S) J k

variable (hgenus : ∀ v : irreducibleComponents (D.subscheme.singularLocus k).blowup,
    (D.subscheme.blowupComponent (K := k) v).toScheme.genus k = 0)

/-- A boundary-orthogonal surface class restricts to a class in the normalization kernel
of a nodal Cartier boundary with genus-zero normalized components. -/
def restrictBoundaryOrthogonal : Multiplicative K[X,D] →* PicZero :=
  let f := (pullbackHom D.subschemeι).comp
    (AddMonoidHom.toMultiplicativeLeft (K[X,D]).subtype.toAddMonoidHom)
  f.codRestrict PicZero fun a ↦ by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, pullbackHom_apply, pullbackHom_apply,
      pullback_comp]
    exact (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal
      hgenus a.toAdd.val).mpr a.toAdd.property

/-- The underlying line-bundle class of a boundary-orthogonal restriction is the
ordinary pullback to the boundary. -/
@[simp]
theorem restrictBoundaryOrthogonal_apply (a : Multiplicative K[X,D]) :
    (hD.restrictBoundaryOrthogonal hgenus a).val = pullback D.subschemeι a.toAdd.val.toMul := by
  simp only [restrictBoundaryOrthogonal, MonoidHom.codRestrict_apply]
  exact pullbackHom_apply _ _

include hD hgenus in
/-- The class of an effective Cartier divisor disjoint from the boundary lies in the
boundary orthogonal. -/
theorem effectiveCartierClass_mem_orthogonal_of_disjoint {E : X.IdealSheafData}
    (hE : E.IsEffectiveCartier) (h : Disjoint (D.support : Set X) (E.support : Set X)) :
    Additive.ofMul (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹ ∈ K[X,D] := by
  apply (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal hgenus _).mp
  rw [toMul_ofMul, ← pullback_comp, hE.pullback_effectiveCartierClass_eq_one_of_disjoint h,
    pullback_one]

variable {ι : Type v} {p : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus} {n : ℕ} [NeZero n]
  {e : ZMod n ≃ (D.subscheme.dualGraph p).Edge}
  {o : (D.subscheme.dualGraph p).Edge → Equiv.Perm (Fin 2)}
  {w : ZMod n ≃ (D.subscheme.dualGraph p).Vertex}
  (hw : ∀ i b, (D.subscheme.dualGraph p).endpoint (e i) (o (e i) b) =
    w ((DualGraph.cycle n).endpoint i b))

/-- The boundary period character takes the oriented gluing product of the
restriction of a boundary-orthogonal class. -/
def boundaryPeriod : Multiplicative K[X,D] →* kˣ :=
  (Scheme.nodalPicardCycleMulEquiv hw).toMonoidHom.comp (hD.restrictBoundaryOrthogonal hgenus)

/-- Evaluate the boundary period by restriction followed by the oriented Picard equivalence. -/
theorem boundaryPeriod_apply (a : Multiplicative K[X,D]) :
    hD.boundaryPeriod hgenus hw a =
      Scheme.nodalPicardCycleMulEquiv hw (hD.restrictBoundaryOrthogonal hgenus a) :=
  (rfl)

/-- A boundary-orthogonal class has period one exactly when its restriction to
the boundary is trivial. -/
@[simp]
theorem boundaryPeriod_eq_one_iff (a : Multiplicative K[X,D]) :
    hD.boundaryPeriod hgenus hw a = 1 ↔ pullback D.subschemeι a.toAdd.val.toMul = 1 := by
  rw [boundaryPeriod_apply, ← map_one (Scheme.nodalPicardCycleMulEquiv hw),
    (Scheme.nodalPicardCycleMulEquiv hw).injective.eq_iff, ← Subtype.val_inj,
    restrictBoundaryOrthogonal_apply]
  rfl

/-- The divisor class of an effective Cartier divisor disjoint from the boundary lies
in the boundary orthogonal lattice and has period one. This applies in particular
to the class of an internal curve of square `-2`. -/
theorem boundaryPeriod_eq_one_of_disjoint {E : X.IdealSheafData} (hE : E.IsEffectiveCartier)
    (h : Disjoint (D.support : Set X) (E.support : Set X)) :
    let a := Additive.ofMul (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹
    ∃ ha : a ∈ K[X,D], hD.boundaryPeriod hgenus hw (Multiplicative.ofAdd ⟨a, ha⟩) = 1 := by
  exact ⟨hD.effectiveCartierClass_mem_orthogonal_of_disjoint hgenus hE h,
    (hD.boundaryPeriod_eq_one_iff hgenus hw _).mpr
      (hE.pullback_effectiveCartierClass_eq_one_of_disjoint h)⟩

section Pullback

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {E : Y.IdealSheafData} [PrestableFamily (E.subscheme ↘ Spec (.of k))]
  (hE : E.IsEffectiveCartier)

local notation "C'" => IdealSheafData.subscheme E

variable (hgenus' : ∀ v : irreducibleComponents (E.subscheme.singularLocus k).blowup,
    (E.subscheme.blowupComponent (K := k) v).toScheme.genus k = 0)

section OrthogonalPullback

variable (f : X ⟶ Y) (g : D.subscheme ≅ E.subscheme) [g.hom.IsOver (Spec (.of k))]
  (hcomm : D.subschemeι ≫ f = g.hom ≫ E.subschemeι)

/-- A morphism inducing an isomorphism of the nodal boundaries pulls back classes
orthogonal to the target boundary to classes orthogonal to the source boundary. -/
def boundaryOrthogonalPullback : K[Y,E] →ₗ[ℤ] K[X,D] :=
  ((pullbackHom f).toAdditive.toIntLinearMap.comp (K[Y,E]).subtype).codRestrict
    K[X,D] fun b ↦ by
      apply (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal hgenus _).mp
      have hb := (g.nodalPicardKernelPullback (k := k)
        (hE.restrictBoundaryOrthogonal hgenus' (Multiplicative.ofAdd b))).property
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, AddMonoidHom.coe_toIntLinearMap,
        MonoidHom.coe_toAdditive, Function.comp_apply, toMul_ofMul, pullbackHom_apply]
      rw [← pullback_comp (D.subscheme.singularLocus k).blowupToBase D.subschemeι,
        pullback_comp D.subschemeι f, hcomm, ← pullback_comp g.hom E.subschemeι]
      simpa only [MonoidHom.mem_ker, pullbackHom_apply, Iso.coe_nodalPicardKernelPullback,
        restrictBoundaryOrthogonal_apply, toAdd_ofAdd] using hb

/-- The underlying boundary-orthogonal class is the ordinary pullback. -/
@[simp]
theorem coe_boundaryOrthogonalPullback (b : K[Y,E]) :
    (hD.boundaryOrthogonalPullback hgenus hE hgenus' f g hcomm b).val.toMul =
      pullback f b.val.toMul := by
  simp only [boundaryOrthogonalPullback, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, AddMonoidHom.coe_toIntLinearMap, MonoidHom.coe_toAdditive,
    Function.comp_apply, toMul_ofMul, pullbackHom_apply]

end OrthogonalPullback

variable {ι' : Type v'} {p' : ι' → (E.subscheme ↘ Spec (.of k)).smoothLocus} {m : ℕ} [NeZero m]
  {e' : ZMod m ≃ (E.subscheme.dualGraph p').Edge}
  {o' : (E.subscheme.dualGraph p').Edge → Equiv.Perm (Fin 2)}
  {w' : ZMod m ≃ (E.subscheme.dualGraph p').Vertex}
  (hw' : ∀ i b, (E.subscheme.dualGraph p').endpoint (e' i) (o' (e' i) b) =
    w' ((DualGraph.cycle m).endpoint i b))

/-- A morphism restricting to an isomorphism of the boundaries pulls back
boundary-orthogonal classes and preserves or inverts their periods according to
the action on ordered branches. -/
theorem boundaryPeriod_pullback (f : X ⟶ Y) (g : C ≅ C') [g.hom.IsOver (Spec (.of k))]
    (hcomm : D.subschemeι ≫ f = g.hom ≫ E.subschemeι) (swap : Bool)
    (horder : ∀ (z : (Scheme.singularLocus k C).subscheme) (b : Fin 2),
      (g.branchSchemeIso (R := k)).hom ((C).branchOrderOfDualGraph p o z b).val =
        ((C').branchOrderOfDualGraph p' o' ((g.singularLocusIso (R := k)).hom z)
          (if swap then b.rev else b)).val)
    (a : Multiplicative K[Y,E]) :
    let a₀ := Additive.ofMul (pullback f a.toAdd.val.toMul)
    ∃ ha : a₀ ∈ K[X,D],
      hD.boundaryPeriod hgenus hw (Multiplicative.ofAdd ⟨a₀, ha⟩) =
        if swap then (hE.boundaryPeriod hgenus' hw' a)⁻¹ else hE.boundaryPeriod hgenus' hw' a := by
  let b := hD.boundaryOrthogonalPullback hgenus hE hgenus' f g hcomm a.toAdd
  have ha : Additive.ofMul (pullback f a.toAdd.val.toMul) ∈ K[X,D] := by
    rw [← hD.coe_boundaryOrthogonalPullback hgenus hE hgenus' f g hcomm a.toAdd]
    exact b.property
  refine ⟨ha, ?_⟩
  let c := hE.restrictBoundaryOrthogonal hgenus' a
  have hc := g.pullback_mem_ker_pullback_blowupToBase_singularLocus (k := k) c
  have hres : hD.restrictBoundaryOrthogonal hgenus
      (Multiplicative.ofAdd ⟨Additive.ofMul (pullback f a.toAdd.val.toMul), ha⟩) =
        ⟨pullback g.hom c.val, hc⟩ := by
    apply Subtype.ext
    simp only [restrictBoundaryOrthogonal_apply, toAdd_ofAdd, c, toMul_ofMul, pullback_comp,
      hcomm]
  rw [boundaryPeriod_apply, hres, boundaryPeriod_apply]
  exact g.nodalPicardCycleMulEquiv_pullback hw hw' swap horder c

end Pullback

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
