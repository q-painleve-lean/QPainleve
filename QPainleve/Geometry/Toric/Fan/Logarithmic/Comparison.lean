/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Morphism

import QPainleve.AlgebraicGeometry.Morphisms.Modification.Birational
import QPainleve.AlgebraicGeometry.Morphisms.Modification.IsoLocus
import QPainleve.Geometry.Toric.Fan.Logarithmic.Subdivision
import QPainleve.Geometry.Toric.Fan.StarSubdivision.Tower
import QPainleve.Geometry.Toric.Fan.Subdivision.FunctionField
import QPainleve.Geometry.Toric.Fan.TwoDimensional

/-!
# Ordered logarithmic models over a toric subdivision

The orders of rational characters on the pole boundary determine the intermediate
fan of a logarithmic factorization. If a morphism already lifts to a toric
subdivision, its ordered internal blowup model can be used over both targets.
This identifies the specified regular morphisms at the toric steps of the
factorization in [Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable (K : Type) [Field K] [PerfectField K]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ Θ Ω : Fan i}
  {X : Scheme} [IsIntegral X] {P : X.IdealSheafData}

local notation "S" => Spec (CommRingCat.of K)
local notation "X[" A "]" => Fan.finiteFanScheme K A
local notation "π[" H "]" => FanHom.finiteFanSchemeHom K (IsSubdivision.toFanHom H)
local notation "D[" A "," h "]" => Fan.toricBoundaryIdeal K A (IsComplete.nonempty_cones h)

variable {f : X ⟶ Φ.finiteFanScheme K} {g : X ⟶ Ψ.finiteFanScheme K}
  (b : Module.Basis (Fin 2) ℤ N)

variable [IsLocallyNoetherian X] in
/-- The intermediate fan of a factorization into ordered internal blowups and a
toric subdivision is determined by the specified map and its pole boundary.
The orders on the same boundary prime recover the same primitive ray generator
in either factorization. -/
theorem eq_of_toric_internal_factorizations (hc : Φ.IsComplete)
    (hΘ : Θ.IsRegular) (hΩ : Ω.IsRegular) (J : Θ.IsSubdivision Φ) (L : Ω.IsSubdivision Φ)
    {m n : ℕ} (r : Fin m → Θ.Ray) (s : Fin n → Ω.Ray) (c : Fin m → Kˣ) (d : Fin n → Kˣ) :
    letI := hc.nonempty_cones
    letI := J.nonempty_cones_of_nonempty hc.nonempty_cones
    letI := L.nonempty_cones_of_nonempty hc.nonempty_cones
    let A := Θ.internalBlowupTower K b r c
    let B := Ω.internalBlowupTower K b s d
    ∀ (e : A.1 ≅ X) (e' : B.1 ≅ X),
      e.hom ≫ f = A.2.toTower.toBase ≫ π[J] →
      e'.hom ≫ f = B.2.toTower.toBase ≫ π[L] →
      P.comap e.hom = A.2.boundaryι.ker →
      P.comap e'.hom = B.2.boundaryι.ker →
      Θ = Ω := by
  intro A B e e' he he' hP hP'
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Θ.cones := J.nonempty_cones_of_nonempty inferInstance
  let : Nonempty Ω.cones := L.nonempty_cones_of_nonempty inferInstance
  have := Θ.isIntegral_internalBlowupTower K b r c hΘ
  have := Θ.isModification_internalBlowupTower_toBase K b r c hΘ
  have : IsDominant (e.hom ≫ f) := by rw [he]; infer_instance
  have : IsDominant f := IsDominant.of_comp e.hom f
  have hs := congrArg Scheme.IdealSheafData.support hP
  have hs' := congrArg Scheme.IdealSheafData.support hP'
  let R := internalBlowupBoundaryPrimeEquivOfIso K hΘ b r c e hs
  let U := internalBlowupBoundaryPrimeEquivOfIso K hΩ b s d e' hs'
  have hgen {t : Θ.Ray} {u : Ω.Ray} (h : R t = U u) :
      t.primitiveGenerator = u.primitiveGenerator := by
    apply b.repr.injective
    ext j
    let a := (b.coord j).toAddMonoidHom
    exact ((internalBlowupBoundaryPrimeEquivOfIso_eq_iff_forall_ord_character K
      b hΘ J r c e he hs t (U u)).mp h a).symm.trans
      (ord_internalBlowupBoundaryPrimeEquivOfIso_character K b hΩ L s d e' he' hs' u a)
  apply eq_of_range_primitiveGenerator_eq b hΘ hΩ
    (J.isComplete_iff.mpr hc) (L.isComplete_iff.mpr hc)
  rw [← (R.trans U.symm).surjective.range_comp (Ray.primitiveGenerator (Phi := Ω))]
  exact congrArg Set.range (funext fun t ↦ hgen (U.apply_symm_apply (R t)).symm)

variable [X.Over (Spec (.of K))] [X.IsProjectiveOver K]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of K))]
  [f.IsOver (Spec (.of K))] [IsModification f]

/-- When a specified logarithmic morphism already factors through a regular
toric subdivision, a single ordered internal model realizes both projections.
Both projections are the given morphisms on the whole surface, and the
boundary of the internal model is the original pole ideal. -/
theorem IsSubdivision.exists_common_toric_internal_factorization [IsAlgClosed K]
    (H : Ψ.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
    (hfg : g ≫ π[H] = f)
    (hPole : letI := SmoothOfRelativeDimension.smooth 2 (X ↘ S)
      (D[Φ,hc]).comap f = P * ramificationIdealSheaf K f) :
    ∃ (Θ : Fan i) (_ : Θ.IsRegular) (L : Θ.IsSubdivision Ψ),
      letI := (L.trans H).nonempty_cones_of_nonempty hc.nonempty_cones
      ∃ (m : ℕ) (r : Fin m → Θ.Ray) (c : Fin m → Kˣ),
        let A := Θ.internalBlowupTower K b r c
        ∃ e : A.1 ≅ X,
          e.hom ≫ g = A.2.toTower.toBase ≫ π[L] ∧
          e.hom ≫ f = A.2.toTower.toBase ≫ π[L.trans H] ∧
          P.comap e.hom = A.2.boundaryι.ker := by
  subst f
  let hc' := H.isComplete_iff.mpr hc
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Ψ.cones := hc'.nonempty_cones
  have hN : Module.finrank ℤ N = 2 :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : IsModification π[H] := H.isModification_finiteFanSchemeHom K hΦ hΨ hc.nonempty_cones hN
  let : IsModification g := IsModification.of_comp_right g π[H]
  let : g.IsOver S := ⟨by
    rw [Ψ.finiteFanScheme_over K,
      ← H.toFanHom.finiteFanSchemeHom_comp_finiteFanSchemeToSpec K,
      ← Category.assoc, ← Φ.finiteFanScheme_over K, comp_over]⟩
  have hpole' :=
    (H.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff K hΦ hΨ hc hN g P).mp hPole
  obtain ⟨Θ, hΘ, L, m, r, c, e, he, hboundary⟩ :=
    Ψ.exists_toric_internal_factorization_of_boundary_comap_eq K b hΨ hc'
      (IsModification.birationalOver g) hpole'
  refine ⟨Θ, hΘ, L, m, r, c, e, he, ?_, hboundary⟩
  rw [← Category.assoc, he, Category.assoc, IsSubdivision.toFanHom_trans L H,
    FanHom.finiteFanSchemeHom_comp K]

/-- If a logarithmic morphism lifts regularly to a finer toric target, any
specified ordered internal model of the original morphism already refines that
target. Its existing tower, including all labels and infinitely near centers,
recovers the lift by a toric projection. -/
theorem IsSubdivision.exists_lift_of_toric_internal_factorization [IsAlgClosed K]
    (H : Ψ.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
    (hΘ : Θ.IsRegular) (J : Θ.IsSubdivision Φ) {m : ℕ} (r : Fin m → Θ.Ray) (c : Fin m → Kˣ)
    (hfg : g ≫ π[H] = f)
    (hPole : letI := SmoothOfRelativeDimension.smooth 2 (X ↘ S)
      (D[Φ,hc]).comap f = P * ramificationIdealSheaf K f) :
    letI := J.nonempty_cones_of_nonempty hc.nonempty_cones
    let A := Θ.internalBlowupTower K b r c
    ∀ (e : A.1 ≅ X),
      e.hom ≫ f = A.2.toTower.toBase ≫ π[J] →
      P.comap e.hom = A.2.boundaryι.ker →
      ∃ L : Θ.IsSubdivision Ψ, e.hom ≫ g = A.2.toTower.toBase ≫ π[L] := by
  intro A e he hboundary
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Ψ.cones := H.nonempty_cones_of_nonempty inferInstance
  let : Nonempty Θ.cones := J.nonempty_cones_of_nonempty inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  obtain ⟨Ω, hΩ, L, n, s, d, e', -, he', hboundary'⟩ :=
    H.exists_common_toric_internal_factorization K b hΦ hΨ hc hfg hPole
  have h := eq_of_toric_internal_factorizations K b hc hΘ hΩ J (L.trans H) r s c d
    e e' he he' hboundary hboundary'
  subst Ω
  have hN : Module.finrank ℤ N = 2 :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : IsModification π[H] := H.isModification_finiteFanSchemeHom K hΦ hΨ hc.nonempty_cones hN
  let : IsModification (g ≫ π[H]) := hfg.symm ▸ ‹IsModification f›
  let : IsModification g := IsModification.of_comp_right g π[H]
  let : IsIntegral A.1 := Θ.isIntegral_internalBlowupTower K b r c hΘ
  let : IsModification A.2.toTower.toBase :=
    Θ.isModification_internalBlowupTower_toBase K b r c hΘ
  refine ⟨L, Scheme.Hom.eq_of_comp_eq_of_isModification π[H] ?_⟩
  rw [Category.assoc, hfg, he, Category.assoc, ← FanHom.finiteFanSchemeHom_comp K,
    ← IsSubdivision.toFanHom_trans L H]

end TauCeti.Toric.Fan
