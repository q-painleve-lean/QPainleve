/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.HilbertFunction
public import QPainleve.RingTheory.AdicCompletion.HilbertFunction
public import TauCeti.AlgebraicGeometry.IdealSheaf.Module
public import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Cohomology

/-!
# The completed local ring of an exceptional contraction

The Hilbert function of an exceptional curve's thickenings identifies the
completed local base of a contraction with a power series ring in two variables.
The powers of the maximal ideal enter through the kernels of pullback to the
thickenings.

## References

* The Stacks Project, [Lemma 54.16.3](https://stacks.math.columbia.edu/tag/0C2K)
  and [Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
-/

public section

open CategoryTheory Opposite IsLocalRing
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [IsLocalRing R]
  [IsNoetherianRing R] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  {E : X.IdealSheafData}

local notation "Y" => (Spec (CommRingCat.of R))
local notation "𝔪" => maximalIdeal R
local notation "𝔫" => ofIdealTop (Ideal.map
  (CommRingCat.Hom.hom (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of R)))) (maximalIdeal R))

private theorem finrank_quotient_pow_of_exceptional_thickening
    (hE : E.IsExceptionalCurveOfFirstKind) (e : projectiveLine k ≅ E.subscheme)
    [e.hom.IsOver (Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    [IsIso f.appTop] (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ)
    (hK : ((E ^ (n + 1)).sections ⊤).comap
      ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom = 𝔪 ^ (n + 1)) :
    Module.finrank k (R ⧸ 𝔪 ^ (n + 1)) = (n + 2).choose 2 := by
  let Z := (E ^ (n + 1)).subscheme
  let i := (E ^ (n + 1)).subschemeι
  let a := ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ f).appTop).hom
  let : Algebra k Γ(Z, ⊤) := ((Z.baseRingToStructurePresheaf k).app (op ⊤)).hom.toAlgebra
  have hker : RingHom.ker a = 𝔪 ^ (n + 1) := by
    dsimp only [a]
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, CommRingCat.hom_comp, ← RingHom.comap_ker]
    refine (congrArg (Ideal.comap ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) ?_).trans hK
    ext r
    exact (mem_sections_iff (E ^ (n + 1))).symm
  have hsurj : Function.Surjective a := by
    let j := subschemeMap (E ^ (n + 1)) (𝔫 ^ (n + 1)) f (pow_le_map_pow hI.le (n + 1))
    have happ : IsIso (f.app ⊤) := ‹IsIso f.appTop›
    have hj := hE.surjective_appTop_subschemeMap_pow_of_contraction f hI hU
      (U := ⊤) (isAffineOpen_top _) le_top n
    have hi := IsClosedImmersion.isAffine_surjective_of_isAffine (𝔫 ^ (n + 1)).subschemeι
    have hΓ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).surjective
    have ha : i ≫ f = j ≫ (𝔫 ^ (n + 1)).subschemeι := (subschemeMap_subschemeι _ _ _ _).symm
    dsimp only [a]
    rw [ha, Scheme.Hom.comp_appTop]
    exact hj.comp (hi.2.comp hΓ)
  have hbase (c : k) : a (algebraMap k R c) = algebraMap k Γ(Z, ⊤) c := by
    have hf : (i ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
        Z ↘ Spec (.of k) := by
      simpa only [specOverSpec_over] using comp_over (i ≫ f) (Spec (.of k))
    have hg : CommRingCat.ofHom (algebraMap k R) ≫ (Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ f).appTop =
        (Scheme.ΓSpecIso (.of k)).inv ≫ (Z ↘ Spec (.of k)).appTop := by
      rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
        ← Scheme.Hom.comp_appTop, hf]
    rw [RingHom.algebraMap_toAlgebra, Scheme.baseRingToStructurePresheaf_app_top]
    rw [CommRingCat.hom_ofHom, Scheme.Modules.baseRingToGlobalSections_apply]
    have hc := RingHom.congr_fun (congrArg CommRingCat.Hom.hom hg) c
    simpa only [a, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using hc
  let g : R →ₐ[k] Γ(Z, ⊤) := ⟨a, hbase⟩
  let q := (Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := g) hsurj)
  exact q.toLinearEquiv.finrank_eq.trans (hE.finrank_globalSections_thickening e (n + 1))

/-- Suppose pullback along a proper exceptional contraction over a Noetherian local
`k`-algebra identifies global functions, and the map from the base ring to the
functions on the `n`th exceptional thickening has kernel `𝔪 ^ n` for every positive `n`.
Its completed local base is the two-variable formal power series ring over `k`.
The variables map to the images of generators of the maximal ideal of the original local ring. -/
theorem exists_algEquiv_mvPowerSeries_of_exceptional_thickenings
    (hE : E.IsExceptionalCurveOfFirstKind) (e : projectiveLine k ≅ E.subscheme)
    [e.hom.IsOver (Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    [IsIso f.appTop] (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus)
    (hK : ∀ n : ℕ, ((E ^ (n + 1)).sections ⊤).comap
      ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom = 𝔪 ^ (n + 1)) :
    ∃ (φ : MvPowerSeries (Fin 2) k ≃ₐ[k] AdicCompletion 𝔪 R) (x : Fin 2 → R),
      Ideal.span (Set.range x) = 𝔪 ∧
        ∀ i, φ (MvPowerSeries.X i) = algebraMap R (AdicCompletion 𝔪 R) (x i) := by
  apply AdicCompletion.exists_algEquiv_mvPowerSeries_of_finrank_quotient_pow
  exact fun n ↦ finrank_quotient_pow_of_exceptional_thickening hE e f hI hU n (hK n)

/-- Under the exceptional thickening kernel comparison, the local ring at the contracted
point is regular of dimension two. -/
theorem isRegularLocalRing_and_ringKrullDim_eq_of_exceptional_thickenings
    (hE : E.IsExceptionalCurveOfFirstKind) (e : projectiveLine k ≅ E.subscheme)
    [e.hom.IsOver (Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    [IsIso f.appTop] (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus)
    (hK : ∀ n : ℕ, ((E ^ (n + 1)).sections ⊤).comap
      ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom = 𝔪 ^ (n + 1)) :
    IsRegularLocalRing R ∧ ringKrullDim R = 2 :=
  AdicCompletion.isRegularLocalRing_and_ringKrullDim_eq_of_finrank_quotient_pow
    (k := k) 2 fun n ↦ finrank_quotient_pow_of_exceptional_thickening hE e f hI hU n (hK n)

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
