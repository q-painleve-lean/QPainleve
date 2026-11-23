/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.CartierDivisor.LocalEquation
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.AffineLine
import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange
import TauCeti.AlgebraicGeometry.IdealSheaf.Locality
import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample

/-!
# Point divisors on the projective line

The linear form `X₀ + c X₁` cuts out the point `[1 : -c⁻¹]` for a unit `c`.
Its coefficients in the two standard frames of `𝒪(1)` give the endpoint
values used to compare the gluing of two point ideals on a nodal boundary.

See [Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*,
Proposition 2.9](https://arxiv.org/html/1211.6367v5#S2).
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open HomogeneousLocalization Opposite Polynomial
open Scheme.IdealSheafData Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R : Type u) [CommRing R]

local notation "𝒜" => TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)
local notation "P" => projectiveLine R
local notation "U[" i "]" => Proj.basicOpen 𝒜 (coord R i)
local notation "j[" i "]" => polynomialChartι R i

/-- The twisting sheaf `𝒪(1)` on the projective line, as an invertible sheaf. -/
abbrev twistingSheafOne : InvertibleSheaf P :=
  ⟨Proj.twistingSheaf 𝒜 1, inferInstance⟩

local notation "L" => twistingSheafOne R

private def binomialForm (c : R) : 𝒜 1 :=
  ⟨coord R 0 + c • coord R 1, (𝒜 1).add_mem (coord_mem R 0) ((𝒜 1).smul_mem _ (coord_mem R 1))⟩

/-- The section of `𝒪(1)` represented by the homogeneous form `X₀ + c X₁`. -/
def binomialSection (c : R) : Γ((L).obj, ⊤) :=
  Proj.toTwistingSheaf 𝒜 rfl ⊤ (binomialForm R c)

local notation "M" => Proj.twistingSheaf 𝒜 1
local notation "frame[" i "]" =>
  Proj.twistingSheaf.chartGenerator 1 (coord R i) (coord_mem R i) U[i] le_rfl

private theorem binomialSection_restrict (c : R) (i : Fin 2) :
    (M).presheaf.map (U[i]).leTop.op (binomialSection R c) =
      (Proj.awayToSection 𝒜 (coord R i)
        (Away.mk 𝒜 (coord_mem R i) 1 (binomialForm R c)
          (by simpa only [one_nsmul] using (binomialForm R c).property))) • frame[i] := by
  rw [binomialSection, Proj.res_toTwistingSheaf]
  exact Proj.twistingSheaf.toTwistingSheaf_eq_smul_chartGenerator 1 _ (coord_mem R i)

/-- In the standard frame on chart `i`, the coefficient of the binomial section is
`1 + cX` on the first chart and `X + c` on the second. -/
theorem binomialSection_chart (c : R) (i : Fin 2) :
    (Scheme.ΓSpecIso (.of R[X])).hom
      (j[i].appLE U[i] ⊤ (preimage_polynomialChartι_basicOpen_self R i).ge
        ((M).sectionRatio ((M).presheaf.map (U[i]).leTop.op (binomialSection R c)) frame[i]
          (by rw [Proj.twistingSheaf.nonvanishingLocus_chartGenerator]))) =
    if i = 0 then 1 + C c * X else X + C c := by
  rw [((M).sectionRatio_eq_iff (by rw [Proj.twistingSheaf.nonvanishingLocus_chartGenerator])).mpr
      (binomialSection_restrict R c i).symm, appLE_polynomialChartι_awayToSection,
    awayEquivPolynomial_mk]
  have h : ∀ i : Fin 2, dehomogenize R i (binomialForm R c) =
      if i = 0 then 1 + C c * X else X + C c := by
    rw [Fin.forall_fin_two]
    exact ⟨by simpa [binomialForm] using dehomogenize_coord_zero_add_smul c,
      by simpa [binomialForm] using dehomogenize_coord_one_add_smul c⟩
  exact h i

/-- On a polynomial chart point the pulled-back binomial section is its evaluated
chart polynomial times the pulled-back standard frame. The coefficients at the two
coordinate endpoints are `1` and `c` when the coefficient map is the identity. -/
theorem pullbackSections_binomialSection {A : Type u} [CommRing A]
    (f : R →+* A) (i : Fin 2) (a : A) (c : R) :
    let p := polynomialPoint R f i a
    p.pullbackSectionsLE M ⊤ ⊤ (Scheme.Hom.preimage_top p).ge (binomialSection R c) =
      (Scheme.ΓSpecIso (.of A)).inv (if i = 0 then 1 + f c * a else a + f c) •
        p.pullbackSectionsLE M U[i] ⊤ (preimage_polynomialPoint_basicOpen_self R f i a).ge
          frame[i] := by
  dsimp only
  let p := polynomialPoint R f i a
  let h := (preimage_polynomialPoint_basicOpen_self R f i a).ge
  let b := (M).sectionRatio ((M).presheaf.map (U[i]).leTop.op (binomialSection R c)) frame[i]
    (by rw [Proj.twistingSheaf.nonvanishingLocus_chartGenerator])
  have hb : b • frame[i] = (M).presheaf.map (U[i]).leTop.op (binomialSection R c) :=
    (M).sectionRatio_smul _ _ _
  have he := congrArg (p.pullbackSectionsLE M U[i] ⊤ h) hb
  rw [map_smulₛₗ, p.pullbackSectionsLE_map M ⊤ ⊤ (Scheme.Hom.preimage_top p).ge
    (U[i]).leTop h] at he
  have hc : p.appLE U[i] ⊤ h b =
      (Scheme.ΓSpecIso (.of A)).inv (if i = 0 then 1 + f c * a else a + f c) := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).hom).injective
    rw [Iso.inv_hom_id_apply, appLE_polynomialPoint, binomialSection_chart]
    by_cases hi : i = 0 <;> simp [hi]
  rw [hc] at he
  exact he.symm

/-- The ratio of two binomial sections at `[1 : 0]` is one and at `[0 : 1]`
it is `c/d`, where the second section has a unit parameter `d`. -/
theorem pullbackSections_binomialSection_zero_eq_smul (i : Fin 2) (c : R) (d : Rˣ) :
    let p := polynomialPoint R (RingHom.id R) i 0
    p.pullbackSectionsLE M ⊤ ⊤ (Scheme.Hom.preimage_top p).ge (binomialSection R c) =
      (Scheme.ΓSpecIso (.of R)).inv (if i = 0 then 1 else c * ↑d⁻¹) •
        p.pullbackSectionsLE M ⊤ ⊤ (Scheme.Hom.preimage_top p).ge
          (binomialSection R (d : R)) := by
  dsimp only
  rw [pullbackSections_binomialSection R (RingHom.id R) i 0 c,
    pullbackSections_binomialSection R (RingHom.id R) i 0 (d : R)]
  split_ifs with hi
  · simp only [RingHom.id_apply, mul_zero, add_zero, map_one]
    rw [one_smul, one_smul]
  · simp only [RingHom.id_apply, zero_add]
    rw [smul_smul]
    have h := ((Scheme.ΓSpecIso (.of R)).inv.hom).map_mul (c * (↑d⁻¹ : R)) (↑d : R)
    rw [← h, mul_assoc, Units.inv_mul, mul_one]

private theorem zeroIdeal_binomialSection_comap (c : R) (i : Fin 2) :
    ((L).zeroIdeal (binomialSection R c)).comap j[i] =
      (if i = 0 then 1 + C c * X else X + C c : R[X]).zeroIdealSheaf := by
  let U : (P).affineOpens := ⟨U[i], isAffineOpen_basicOpen_coord R i⟩
  let V : (Spec (.of R[X])).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  rw [Polynomial.zeroIdealSheaf_eq_ofIdealTop]
  -- Use the order-ring equivalence explicitly so its inverse simplifies to the affine ideal.
  refine (equivOfIsAffine (X := Spec (.of R[X]))).injective
    (show equivOfIsAffine _ = equivOfIsAffine _ from ?_)
  rw [← equivOfIsAffine_symm_apply, OrderRingIso.apply_symm_apply, equivOfIsAffine_apply]
  rw [ideal_comap_of_le _ j[i] U V (preimage_polynomialChartι_basicOpen_self R i).ge,
    (L).zeroIdeal_ideal_eq_span_singleton _ U frame[i]
      (by rw [Proj.twistingSheaf.nonvanishingLocus_chartGenerator]),
    Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  apply congrArg (fun a ↦ Ideal.span {a})
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R[X])).hom).injective
  rw [Iso.inv_hom_id_apply]
  exact binomialSection_chart R c i

private theorem ker_polynomialPoint_comap_chart (i : Fin 2) (a : R) :
    (polynomialPoint R (RingHom.id R) i a).ker.comap j[i] = (X - C a).zeroIdealSheaf := by
  let p := polynomialPoint R (RingHom.id R) i a
  let f := Spec.map (CommRingCat.ofHom (evalRingHom a))
  have hp : p = f ≫ j[i] := polynomialPoint_def R (RingHom.id R) i a
  have : IsClosedImmersion p := p.isClosedImmersion_of_comp_eq_id
    (f := P ↘ Spec (.of R)) (by simp [p, polynomialPoint_over])
  have h : IsPullback f (𝟙 _) j[i] p :=
    IsPullback.of_vert_isIso_mono ⟨by rw [← hp, Category.id_comp]⟩
  rw [← ker_eq_comap_of_isPullback_of_isOpenImmersion j[i] h,
    Polynomial.zeroIdealSheaf_eq_ofIdealTop, Scheme.Hom.ker_Spec_map,
    CommRingCat.hom_ofHom, ker_evalRingHom]

/-- The zero scheme of `X₀ + c X₁` is the actual closed point section `[1 : −c⁻¹]`
over the coefficient ring. -/
theorem zeroIdeal_binomialSection (c : Rˣ) :
    (L).zeroIdeal (binomialSection R (c : R)) =
      (polynomialPoint R (RingHom.id R) 0 (-(↑c⁻¹ : R))).ker := by
  let cover : (P).OpenCover := Scheme.Cover.mkOfCovers (Fin 2) _ (polynomialChartι R) fun x ↦ by
    have hx : x ∈ Set.range (j[0]) ∪ Set.range (j[1]) := by
      rw [range_polynomialChartι_union_range_polynomialChartι]
      trivial
    rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨0, y, hy⟩
    · exact ⟨1, y, hy⟩
  suffices h : ∀ i : Fin 2, ((L).zeroIdeal (binomialSection R (c : R))).comap j[i] =
      (polynomialPoint R (RingHom.id R) 0 (-(↑c⁻¹ : R))).ker.comap j[i] from
    ext_of_comap_openCover cover h
  rw [Fin.forall_fin_two]
  constructor
  · rw [zeroIdeal_binomialSection_comap, ite_eq_left rfl, ker_polynomialPoint_comap_chart,
      Polynomial.zeroIdealSheaf_eq_ofIdealTop, Polynomial.zeroIdealSheaf_eq_ofIdealTop]
    have hc : 1 + C (c : R) * X = C (c : R) * (X - C (-(↑c⁻¹ : R))) := by
      rw [mul_sub, ← map_mul]
      simp [add_comm]
    rw [hc, Ideal.span_singleton_mul_left_unit (c.isUnit.map C)]
  · have hp := polynomialPoint_rev (RingHom.id R) 0 (-c⁻¹)
    have hp' : polynomialPoint R (RingHom.id R) 0 (-(↑c⁻¹ : R)) =
        polynomialPoint R (RingHom.id R) 1 (-(c : R)) := by
      simpa using hp
    rw [zeroIdeal_binomialSection_comap, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), hp',
      ker_polynomialPoint_comap_chart]
    simp only [map_neg, sub_neg_eq_add]

end TauCeti.AlgebraicGeometry.projectiveLine
