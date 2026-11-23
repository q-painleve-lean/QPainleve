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
  (LinearMap.BilinForm.orthogonal (Chow.intersectionBilinForm k S)
    (@Scheme.Opens.primeDivisorSpanCompl S
      (LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (CommRingCat.of k))) inferInstance
      (Scheme.Hom.uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
        (S ↘ Spec (CommRingCat.of k)))
      (Closeds.compl (IdealSheafData.support J))))

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
  have hcomap : E.comap D.subschemeι = ⊤ := by
    apply (E.comap_eq_top_iff _).mpr
    ext x
    simpa using Set.disjoint_left.mp h (D.range_subschemeι.le (Set.mem_range_self x))
  have hres : pullback D.subschemeι (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹ = 1 := by
    rw [pullback_inv, hE.pullback_mk_toInvertibleSheaf_eq_one_of_comap_eq_top hcomap, inv_one]
  have ha := (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal
    hgenus (Additive.ofMul (LineBundleClass.mk hE.toInvertibleSheaf)⁻¹)).mp
    (by rw [toMul_ofMul, ← pullback_comp, hres, pullback_one])
  exact ⟨ha, (hD.boundaryPeriod_eq_one_iff hgenus hw _).mpr hres⟩

section Pullback

variable {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsProjectiveOver k] [IsIntegral Y]
  [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k))]
  {E : Y.IdealSheafData} [PrestableFamily (E.subscheme ↘ Spec (.of k))]
  (hE : E.IsEffectiveCartier)

local notation "C'" => IdealSheafData.subscheme E

variable (hgenus' : ∀ v : irreducibleComponents (E.subscheme.singularLocus k).blowup,
    (E.subscheme.blowupComponent (K := k) v).toScheme.genus k = 0)
  {ι' : Type v'} {p' : ι' → (E.subscheme ↘ Spec (.of k)).smoothLocus} {m : ℕ} [NeZero m]
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
  let b := hE.restrictBoundaryOrthogonal hgenus' a
  have hb := g.pullback_mem_ker_pullback_blowupToBase_singularLocus b
  have hrestrict : pullback D.subschemeι (pullback f a.toAdd.val.toMul) =
      pullback g.hom b.val := by
    simp only [b, restrictBoundaryOrthogonal_apply, pullback_comp, hcomm]
  have ha := (hD.pullback_blowupToBase_comp_subschemeι_eq_one_iff_mem_orthogonal
    hgenus (Additive.ofMul (pullback f a.toAdd.val.toMul))).mp (by
    rw [toMul_ofMul, ← pullback_comp, hrestrict, ← pullbackHom_apply]
    exact MonoidHom.mem_ker.mp hb)
  refine ⟨ha, ?_⟩
  have hb' : hD.restrictBoundaryOrthogonal hgenus
      (Multiplicative.ofAdd ⟨Additive.ofMul (pullback f a.toAdd.val.toMul), ha⟩) =
        ⟨pullback g.hom b.val, hb⟩ :=
    Subtype.ext ((restrictBoundaryOrthogonal_apply ..).trans hrestrict)
  rw [boundaryPeriod_apply, hb', boundaryPeriod_apply]
  exact g.nodalPicardCycleMulEquiv_pullback hw hw' swap horder b

end Pullback

end AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier
