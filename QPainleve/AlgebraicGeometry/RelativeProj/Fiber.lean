/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.ProjectiveBundle
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
public import Mathlib.AlgebraicGeometry.Fiber

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Polynomial.BaseChange

/-!
# Fibers of projective bundles

The fiber of the relative projective spectrum of a vector bundle is polynomial projective
space over the residue field. The identification preserves the projection and every
integral twist, in particular the polarization of the fibers of a rank-two bundle.

We use the polynomial charts and coefficient base change, as in the quotient convention
of [Stacks, Section 27.21][stacks-01OA].

[stacks-01OA]: https://stacks.math.columbia.edu/tag/01OA
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {r : ℕ} (E : FixedRank X r) (x : X)

local notation "κ[" x "]" => Scheme.residueField X x

/-- The scheme-theoretic fiber of a projective bundle of rank `r` is the polynomial
projective spectrum on `r` variables over the residue field. The same isomorphism
identifies all integral twists with the restrictions of the relative twists. -/
theorem exists_relativeProj_fiber_iso :
    let A := ((gradedSymmetricAlgebra X).obj
      ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj)).obj
    let p := A.relativeProjToBase
    let P := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin r)) κ[x]
    ∃ e : Proj P ≅ p.fiber x,
      e.hom ≫ p.fiberToSpecResidueField x = Proj.toSpecCoeff P ∧
      ∀ n : ℤ, Nonempty
        ((Scheme.Modules.pullback (e.hom ≫ p.fiberι x)).obj (A.relativeProjTwistingSheaf n) ≅
          Proj.twistingSheaf P n) := by
  obtain ⟨U, hxU, -, j, hj, htwist⟩ :=
    E.exists_relativeProjPolynomialChart (x := x) (W := ⊤) (by simp)
  let A := ((gradedSymmetricAlgebra X).obj
    ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj)).obj
  let p := A.relativeProjToBase
  let R := Γ(X, U.toOpens)
  let f := U.property.fromSpec
  have hmem : Set.range (X.fromSpecResidueField x) ⊆ Set.range f := by
    rw [Scheme.range_fromSpecResidueField, Set.singleton_subset_iff, IsAffineOpen.range_fromSpec]
    exact hxU
  let s := IsOpenImmersion.lift f (X.fromSpecResidueField x) hmem
  have hs : s ≫ f = X.fromSpecResidueField x := IsOpenImmersion.lift_fac _ _ _
  let : Algebra R κ[x] := (Spec.preimage s).hom.toAlgebra
  let coords := ULift.{u} (Fin r)
  let P := MvPolynomial.homogeneousSubmodule coords R
  let q := Proj.polynomialBaseChangeProjection (R := R) (S := κ[x]) coords
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap R κ[x])) = s := Spec.map_preimage s
  have hchart : IsPullback j (Proj.toSpecCoeff P) p f := by
    have hAffine : IsPullback (𝟙 (Proj P)) (Proj.toSpecCoeff P)
        (Proj.toSpecCoeff P ≫ U.property.isoSpec.inv) U.property.isoSpec.inv :=
      IsPullback.of_horiz_isIso ⟨Category.id_comp _⟩
    simpa only [Category.id_comp, IsAffineOpen.isoSpec_inv_ι, f] using hAffine.paste_horiz hj.flip
  have hq := Proj.isPullback_polynomialBaseChangeProjection (R := R) (S := κ[x]) coords
  rw [hbase] at hq
  have h := hq.paste_horiz hchart
  rw [hs] at h
  let e : Proj (MvPolynomial.homogeneousSubmodule coords κ[x]) ≅ p.fiber x := h.isoPullback
  refine ⟨e, h.isoPullback_hom_snd, fun n ↦ ?_⟩
  have he : e.hom ≫ p.fiberι x = q ≫ j := h.isoPullback_hom_fst
  exact ⟨(Scheme.Modules.pullbackCongr he).app _ ≪≫
    (Scheme.Modules.pullbackComp q j).symm.app _ ≪≫
    (Scheme.Modules.pullback q).mapIso (htwist n).some ≪≫
    Proj.polynomialBaseChangeProjectionPullbackTwistingSheafIso _ n⟩

/-- Every fiber of a rank-two projective bundle is a projective line over the residue
field, and its relative polarization restricts to the degree-one twisting class. -/
theorem exists_relativeProj_fiber_iso_projectiveLine (E : FixedRank X 2) (x : X) :
    let A := ((gradedSymmetricAlgebra X).obj
      ((FiniteLocallyFreeSheaf.toQuasicoherent X).obj E.obj)).obj
    let p := A.relativeProjToBase
    let L : InvertibleSheaf A.relativeProj := ⟨A.relativeProjTwistingSheaf 1, inferInstance⟩
    ∃ e : projectiveLine κ[x] ≅ p.fiber x,
      e.hom ≫ p.fiberToSpecResidueField x = (projectiveLine κ[x] ↘ Spec (.of κ[x])) ∧
      LineBundleClass.pullback e.hom (LineBundleClass.pullback (p.fiberι x)
        (LineBundleClass.mk L)) =
        LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle κ[x] (Fin 2 → κ[x]) 1) := by
  obtain ⟨e, he, ht⟩ := E.exists_relativeProj_fiber_iso x
  let b : Module.Basis (ULift.{u} (Fin 2)) κ[x] (Fin 2 → κ[x]) :=
    (Pi.basisFun κ[x] (Fin 2)).reindex Equiv.ulift.symm
  let i := b.polynomialProjIso
  refine ⟨i.symm ≪≫ e, ?_, ?_⟩
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, he, ← b.polynomialProjIso_hom_over]
    exact i.inv_hom_id_assoc _
  · apply (LineBundleClass.pullbackEquiv i).injective
    simp only [LineBundleClass.pullbackEquiv_apply, Iso.trans_hom, Iso.symm_hom]
    rw [LineBundleClass.pullback_comp i.hom (i.inv ≫ e.hom), i.hom_inv_id_assoc,
      LineBundleClass.pullback_comp e.hom]
    simp only [LineBundleClass.pullback_mk, LineBundleClass.mk_eq_mk_iff]
    exact ⟨(ht 1).some ≪≫ (b.polynomialProjIsoPullbackTwistingSheafIso 1).symm⟩

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
