/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.ProjectiveLineCharts
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Scaling

import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.PolynomialComparison
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The projective overlap of a split bundle over the projective line

The standard twisting frames give charts whose fibers are native projective lines.
On the overlap of the two base charts, their change of coordinates is projective
scaling by `(X₁ / X₀)^(a - b)` for the split bundle `𝒪(a) ⊞ 𝒪(b)`. The
comparison uses `QuasicoherentSheaf.relativeProjPolynomialChart`, the split frame
restriction, and `Proj.fromOfGlobalSections_eq_of_X_unit_rescaling`.
-/

public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Proj CategoryTheory Limits Opposite

open QPainleve (map_comp_coordinateComparison projectiveLineCoordinateBasis)

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

private abbrev CoordinateIndex := ULift.{u} (Fin 2)

local notation "𝒫[" A "]" => MvPolynomial.homogeneousSubmodule CoordinateIndex A
local notation "𝒮[" A "]" => TauCeti.SymmetricAlgebra.homogeneousSubmodule A (Fin 2 → A)

variable (R)

local notation "P" => projectiveLine R
local notation "U[" i "]" => Proj.basicOpen 𝒮[R] (coord R i)
local notation "line[" n "]" =>
  Functor.obj (InvertibleSheaf.toFixedRankOne (projectiveLine R))
    (Proj.symmetricAlgebraTwistingBundle R (Fin 2 → R) n)
local notation "F[" a "," b "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent (projectiveLine R))
    (ObjectProperty.FullSubcategory.obj (FiniteLocallyFreeSheaf.FixedRank.biprod line[a] line[b]))
local notation "A[" a "," b "]" =>
  ObjectProperty.FullSubcategory.obj
    (Functor.obj (gradedSymmetricAlgebra (projectiveLine R)) F[a,b])
local notation "Γ[" U "]" => CommRingCat.carrier (Functor.obj
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace (projectiveLine R)))))
  (op (Scheme.AffineZariskiSite.toOpens U)))
local notation "PL[" U "]" => projectiveLine Γ[U]
local notation "q[" U "]" => (PL[U] ↘ Spec (CommRingCat.of Γ[U]))

/-- The chart over an affine subopen of a standard base chart for the projectivization
of `𝒪(a) ⊞ 𝒪(b)`, with the indicated twisting frames as homogeneous coordinates. -/
def relativeProjSplitTwistingChart (a b : ℤ) (i : Fin 2) (U : (P).AffineZariskiSite)
    (h : U.toOpens ≤ U[i]) : PL[U] ⟶ A[a,b].relativeProj :=
  (projectiveLineCoordinateBasis Γ[U]).polynomialProjIso.inv ≫
    (F[a,b]).relativeProjPolynomialChart U (splitTwistingFrame R a b i h)

local notation "chart[" a "," b ";" i "," U "," h "]" =>
  relativeProjSplitTwistingChart R a b i U h

/-- The split chart in terms of the polynomial projective-bundle chart.
The standard basis comparison identifies its homogeneous coordinates with those of `ℙ¹`. -/
theorem relativeProjSplitTwistingChart_def (a b : ℤ) (i : Fin 2)
    (U : (P).AffineZariskiSite) (h : U.toOpens ≤ U[i]) :
    chart[a,b;i,U,h] =
      ((Pi.basisFun Γ[U] (Fin 2)).reindex
        (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2))).polynomialProjIso.inv ≫
        (F[a,b]).relativeProjPolynomialChart U (splitTwistingFrame R a b i h) :=
  (rfl)

/-- The split-twisting chart is the preimage of the indicated affine open of the base. -/
theorem isPullback_relativeProjSplitTwistingChart (a b : ℤ) (i : Fin 2)
    (U : (P).AffineZariskiSite) (h : U.toOpens ≤ U[i]) :
    IsPullback chart[a,b;i,U,h] q[U] A[a,b].relativeProjToBase U.property.fromSpec := by
  let e := (projectiveLineCoordinateBasis Γ[U]).polynomialProjIso
  have he : e.inv ≫ toSpecCoeff 𝒫[Γ[U]] = q[U] := by
    rw [← (projectiveLineCoordinateBasis Γ[U]).polynomialProjIso_hom_over, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
    exact (TauCeti.SymmetricAlgebra.over_eq_projToSpec Γ[U] (Fin 2 → Γ[U])).symm
  have hchart := (F[a,b]).isPullback_relativeProjPolynomialChart U (splitTwistingFrame R a b i h)
  refine hchart.flip.of_iso' e.symm (Iso.refl _) U.property.isoSpec.symm (Iso.refl _)
    (by simp [relativeProjSplitTwistingChart, e]) ?_ (by simp) (by simp)
  simp only [Iso.symm_hom, ← Category.assoc, he]

instance isOpenImmersion_relativeProjSplitTwistingChart (a b : ℤ) (i : Fin 2)
    (U : (P).AffineZariskiSite) (h : U.toOpens ≤ U[i]) :
    IsOpenImmersion chart[a,b;i,U,h] :=
  MorphismProperty.of_isPullback (isPullback_relativeProjSplitTwistingChart R a b i U h).flip
    inferInstance

/-- The split-twisting chart lies over the affine inclusion of its base. -/
@[reassoc (attr := simp)]
theorem relativeProjSplitTwistingChart_toBase (a b : ℤ) (i : Fin 2)
    (U : (P).AffineZariskiSite) (h : U.toOpens ≤ U[i]) :
    chart[a,b;i,U,h] ≫ A[a,b].relativeProjToBase = q[U] ≫ U.property.fromSpec :=
  (isPullback_relativeProjSplitTwistingChart R a b i U h).w

section Restriction

variable {U V : (projectiveLine R).AffineZariskiSite} (j : V ⟶ U)

private abbrev sectionRestriction : Γ[U] →+* Γ[V] :=
  ((P).presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono j.le)).op).hom

private theorem scaling_comp_baseChangeProjection_relativeProjSplitTwistingChart
    (a b : ℤ) (i k : Fin 2) (hi : U.toOpens ≤ U[i]) (hk : V.toOpens ≤ U[k])
    (v w : Γ[V]ˣ)
    (hX : ∀ l : CoordinateIndex,
      (F[a,b]).polynomialSectionsRestrict (splitTwistingFrame R a b i hi) j
        (splitTwistingFrame R a b k hk) (MvPolynomial.X l) =
        (w : Γ[V]) • (if l.down = 0 then (v : Γ[V]) else 1) • MvPolynomial.X l) :
    (scalingBy Γ[V] v).hom ≫ @baseChangeProjection Γ[U] _ Γ[V] _
      ((P).presheaf.map (homOfLE (Scheme.AffineZariskiSite.toOpens_mono j.le)).op).hom.toAlgebra ≫
      chart[a,b;i,U,hi] = chart[a,b;k,V,hk] := by
  let : Algebra Γ[U] Γ[V] := (sectionRestriction R j).toAlgebra
  let f := (F[a,b]).polynomialSectionsRestrict (splitTwistingFrame R a b i hi) j
    (splitTwistingFrame R a b k hk)
  let hf := (F[a,b]).irrelevant_le_map_polynomialSectionsRestrict (splitTwistingFrame R a b i hi) j
    (splitTwistingFrame R a b k hk)
  have hmap := map_comp_coordinateComparison f hf v w
    ((F[a,b]).polynomialSectionsRestrict_C (splitTwistingFrame R a b i hi) j
      (splitTwistingFrame R a b k hk)) hX
  simp only [relativeProjSplitTwistingChart]
  rw [← reassoc_of% hmap,
    (F[a,b]).map_polynomialSectionsRestrict_comp_relativeProjPolynomialChart]

/-- Restriction within a standard base chart preserves the split homogeneous
coordinates, with the coefficients pulled back to the smaller affine open. -/
@[reassoc]
theorem baseChangeProjection_comp_relativeProjSplitTwistingChart
    (a b : ℤ) (i : Fin 2) (hi : U.toOpens ≤ U[i]) :
    let hVU : V.toOpens ≤ U.toOpens := Scheme.AffineZariskiSite.toOpens_mono j.le
    @baseChangeProjection Γ[U] _ Γ[V] _
      ((P).presheaf.map (homOfLE hVU).op).hom.toAlgebra ≫
      chart[a,b;i,U,hi] = chart[a,b;i,V,hVU.trans hi] := by
  intro hVU
  let : Algebra Γ[U] Γ[V] := (sectionRestriction R j).toAlgebra
  have hscale : (scalingBy Γ[V] (1 : Γ[V]ˣ)).hom = 𝟙 _ := by
    have : IsSeparated (terminal.from PL[V]) := by
      rw [← terminal.comp_from q[V]]
      infer_instance
    refine TauCeti.ext_of_isSchemeTheoreticallyDominant (polynomialChartι Γ[V] 1)
      (terminal.from _) (terminal.hom_ext _ _) ?_
    rw [Category.comp_id, ← polynomialPoint_X, polynomialPoint_comp_scalingBy]
    simp
  rw [← Category.id_comp (baseChangeProjection Γ[U] Γ[V] ≫ chart[a,b;i,U,hi]), ← hscale]
  apply scaling_comp_baseChangeProjection_relativeProjSplitTwistingChart R j a b i i hi _ 1 1
  intro k
  have hres : (F[a,b]).obj.val.map
      ((Scheme.AffineZariskiSite.toOpensFunctor (P)).map j).op (splitTwistingFrame R a b i hi k) =
      splitTwistingFrame R a b i (hVU.trans hi) k :=
    restrict_splitTwistingFrame R a b i (homOfLE hVU) hi k
  rw [(F[a,b]).polynomialSectionsRestrict_X, hres, Module.Basis.repr_self,
    Finsupp.sum_single_index (by simp)]
  simp

/-- On an affine open of the overlap, the second split chart precomposed with
projective scaling by `(X₁ / X₀)^(a - b)` agrees with the first split chart. -/
private theorem scalingBy_comp_baseChangeProjection_relativeProjSplitTwistingChart_one
    (a b : ℤ) (h₁ : U.toOpens ≤ U[1]) (h₀ : V.toOpens ≤ U[0]) :
    let hVU : V.toOpens ≤ U.toOpens := Scheme.AffineZariskiSite.toOpens_mono j.le
    let t := affineCoordinateUnit R h₀ (hVU.trans h₁)
    (scalingBy Γ[V] (t ^ (a - b))).hom ≫ @baseChangeProjection Γ[U] _ Γ[V] _
      ((P).presheaf.map (homOfLE hVU).op).hom.toAlgebra ≫
      chart[a,b;1,U,h₁] = chart[a,b;0,V,h₀] := by
  intro hVU t
  let : Algebra Γ[U] Γ[V] := (sectionRestriction R j).toAlgebra
  apply scaling_comp_baseChangeProjection_relativeProjSplitTwistingChart R j a b 1 0 h₁ h₀ _ (t ^ b)
  intro k
  have hx := DFunLike.congr_fun
    (polynomialSectionsRestrict_splitTwistingFrame R a b j h₁ h₀) (MvPolynomial.X k)
  rw [MvPolynomial.eval₂Hom_X'] at hx
  simp only [GradedRingHom.coe_toRingHom] at hx
  rw [hx, smul_smul]
  by_cases hk : k.down = 0
  · have he : b + (a - b) = a := by omega
    simp only [hk, ite_true, ← Units.val_mul, ← zpow_add, he, t]
  · simp [hk, t]

end Restriction

/-- Over a common affine subopen of the two standard charts, the change from the
chart-zero frame to the chart-one frame multiplies the first homogeneous coordinate
by `(X₁ / X₀)^(a - b)` and leaves the second coordinate fixed. -/
theorem relativeProjSplitTwistingChart_overlap (a b : ℤ)
    {U₀ U₁ V : (projectiveLine R).AffineZariskiSite} (j₀ : V ⟶ U₀) (j₁ : V ⟶ U₁)
    (h₀ : U₀.toOpens ≤ U[0]) (h₁ : U₁.toOpens ≤ U[1]) :
    let hV₀ := Scheme.AffineZariskiSite.toOpens_mono j₀.le
    let hV₁ := Scheme.AffineZariskiSite.toOpens_mono j₁.le
    let t := affineCoordinateUnit R (hV₀.trans h₀) (hV₁.trans h₁)
    let p₀ := @baseChangeProjection Γ[U₀] _ Γ[V] _ ((P).presheaf.map (homOfLE hV₀).op).hom.toAlgebra
    let p₁ := @baseChangeProjection Γ[U₁] _ Γ[V] _ ((P).presheaf.map (homOfLE hV₁).op).hom.toAlgebra
    p₀ ≫ chart[a,b;0,U₀,h₀] = (scalingBy Γ[V] (t ^ (a - b))).hom ≫ p₁ ≫ chart[a,b;1,U₁,h₁] :=
  (baseChangeProjection_comp_relativeProjSplitTwistingChart R j₀ a b 0 h₀).trans
    (scalingBy_comp_baseChangeProjection_relativeProjSplitTwistingChart_one R j₁ a b h₁
      ((Scheme.AffineZariskiSite.toOpens_mono j₀.le).trans h₀)).symm

end TauCeti.AlgebraicGeometry.projectiveLine
