/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
public import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.HilbertFunction
public import QPainleve.RingTheory.AdicCompletion.HilbertFunction
public import TauCeti.AlgebraicGeometry.IdealSheaf.Module
public import TauCeti.AlgebraicGeometry.IdealSheaf.OfIdealTop
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Cohomology
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.LocalFiltration
import QPainleve.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Localization

/-!
# The completed local ring of an exceptional contraction

The Hilbert function of an exceptional curve's thickenings identifies the
completed local base of a contraction with a power series ring in two variables.
The powers of the maximal ideal enter through the kernels of pullback to the
thickenings. Localizing at the contracted point gives regularity and dimension
two for its stalk.

## References

* The Stacks Project, [Lemma 54.16.3](https://stacks.math.columbia.edu/tag/0C2K)
  and [Lemma 54.16.4](https://stacks.math.columbia.edu/tag/0C2L).
-/

public section

open CategoryTheory IsLocalRing Limits Opposite TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind

section Affine

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
    [IsIso f.appTop] (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus) (n : ℕ) :
    Module.finrank k (R ⧸ 𝔪 ^ (n + 1)) = (n + 2).choose 2 := by
  let Z := (E ^ (n + 1)).subscheme
  let i := (E ^ (n + 1)).subschemeι
  let a := ((Scheme.ΓSpecIso (.of R)).inv ≫ (i ≫ f).appTop).hom
  let : Algebra k Γ(Z, ⊤) := ((Z.baseRingToStructurePresheaf k).app (op ⊤)).hom.toAlgebra
  have hker : RingHom.ker a = 𝔪 ^ (n + 1) := by
    dsimp only [a]
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, CommRingCat.hom_comp, ← RingHom.comap_ker]
    rw [← comap_sections_pow_of_exceptional_contraction f hE hI hU (n + 1)]
    congr 1
    ext r
    exact (mem_sections_iff (E ^ (n + 1))).symm
  have hsurj : Function.Surjective a := by
    dsimp only [a]
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, CommRingCat.hom_comp]
    exact (hE.surjective_appTop_subschemeι_pow_of_contraction f hI hU (n + 1)).comp
      (ConcreteCategory.bijective_of_isIso
        ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop)).surjective
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

/-- If pullback along a proper exceptional contraction over a Noetherian local `k`-algebra
identifies global functions, its completed local base is the two-variable formal power
series ring over `k`.
The variables map to the images of generators of the maximal ideal of the original local ring. -/
theorem exists_algEquiv_mvPowerSeries_of_exceptional_thickenings
    (hE : E.IsExceptionalCurveOfFirstKind) (e : projectiveLine k ≅ E.subscheme)
    [e.hom.IsOver (Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    [IsIso f.appTop] (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus) :
    ∃ (φ : MvPowerSeries (Fin 2) k ≃ₐ[k] AdicCompletion 𝔪 R) (x : Fin 2 → R),
      Ideal.span (Set.range x) = 𝔪 ∧
        ∀ i, φ (MvPowerSeries.X i) = algebraMap R (AdicCompletion 𝔪 R) (x i) := by
  apply AdicCompletion.exists_algEquiv_mvPowerSeries_of_finrank_quotient_pow
  exact finrank_quotient_pow_of_exceptional_thickening hE e f hI hU

/-- If pullback along a proper exceptional contraction identifies global functions, the
local ring at the contracted point is regular of dimension two. -/
theorem isRegularLocalRing_and_ringKrullDim_eq_of_exceptional_thickenings
    (hE : E.IsExceptionalCurveOfFirstKind) (e : projectiveLine k ≅ E.subscheme)
    [e.hom.IsOver (Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f]
    [IsIso f.appTop] (hI : (𝔫).comap f = E) (hU : (𝔫).support.compl ≤ f.isoLocus) :
    IsRegularLocalRing R ∧ ringKrullDim R = 2 :=
  AdicCompletion.isRegularLocalRing_and_ringKrullDim_eq_of_finrank_quotient_pow
    (k := k) 2 (finrank_quotient_pow_of_exceptional_thickening hE e f hI hU)

end Affine

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {E : X.IdealSheafData}
variable [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [IsLocallyNoetherian Y]

local notation "A[" p "]" => Y.presheaf.stalk p
local notation "s[" p "]" => Y.fromSpecStalk p
local notation "I[" p "]" => Scheme.Hom.ker (Spec.map (Y.residue p))

/-- A proper contraction whose scheme-theoretic fiber is an exceptional projective line
over the ground field has a regular two-dimensional local ring at its contracted point,
provided pullback identifies functions and the morphism is an isomorphism off the point. -/
theorem isRegularLocalRing_and_ringKrullDim_eq_of_contraction
    (hE : E.IsExceptionalCurveOfFirstKind) (e : projectiveLine k ≅ E.subscheme)
    [e.hom.IsOver (Spec (.of k))] (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] {p : Y}
    (hp : IsClosed ({p} : Set Y)) (hF : (Y.fromSpecResidueField p).ker.comap f = E)
    (hU : ((Y.fromSpecResidueField p).ker.support).compl ≤ f.isoLocus)
    (hf : ∀ V : Y.affineOpens, IsIso (f.app V)) :
    IsRegularLocalRing A[p] ∧ ringKrullDim A[p] = 2 := by
  let a := pullback.fst f s[p]
  let g := pullback.snd f s[p]
  let J := I[p].comap g
  -- Use the algebra structure induced by the target scheme at the contracted point.
  let : Algebra k A[p] := (Spec.preimage (s[p] ≫ (Y ↘ Spec (.of k)))).hom.toAlgebra
  let : (pullback f s[p]).Over (Spec (.of k)) := ⟨a ≫ (X ↘ Spec (.of k))⟩
  have ha : a.IsOver (Spec (.of k)) := ⟨rfl⟩
  have hg : g.IsOver (Spec (.of k)) := by
    constructor
    rw [specOverSpec_over]
    have h : Spec.map (CommRingCat.ofHom (algebraMap k A[p])) =
        s[p] ≫ (Y ↘ Spec (.of k)) := Spec.map_preimage _
    rw [h, ← Category.assoc, ← pullback.condition, Category.assoc, comp_over f]
    exact ha.comp_over
  obtain ⟨_, hΓ, hJ, hloc⟩ := hE.localize_contraction hp hF hU hf
  have : IsIso g.appTop := hΓ ⊤
  -- The closed fiber of the localization is the original curve over the ground field.
  have hJE : J = E.comap a := f.comap_ker_residue_pullback_snd_fromSpecStalk hp hF
  let j := subschemeMap J E a (hJE ▸ E.le_map_comap a)
  have : IsIso j := f.isIso_subschemeMap_comap_pullback_fst_of_support_le hp hF E le_rfl hJE
  have hj : j.IsOver (Spec (.of k)) := by
    constructor
    rw [J.over_eq_subschemeι_comp, E.over_eq_subschemeι_comp, ← ha.comp_over]
    exact (reassoc_of% (subschemeMap_subschemeι J E a (hJE ▸ E.le_map_comap a))) (X ↘ Spec (.of k))
  let e' := e ≪≫ (asIso j).symm
  have : e'.hom.IsOver (Spec (.of k)) := by
    dsimp only [e', Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have hI := Scheme.Hom.ker_Spec_map (Y.residue p)
  have hker : RingHom.ker (Y.residue p).hom = IsLocalRing.maximalIdeal A[p] :=
    IsLocalRing.ker_residue
  rw [hker] at hI
  exact hJ.isRegularLocalRing_and_ringKrullDim_eq_of_exceptional_thickenings e' g
    (congrArg (fun K ↦ K.comap g) hI.symm) (hI ▸ hloc)

end AlgebraicGeometry.Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind
