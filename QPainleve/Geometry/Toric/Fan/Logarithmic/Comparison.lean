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

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ Ψ Θ Ω : Fan i}
  {X : Scheme} [IsIntegral X] {P : X.IdealSheafData}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" A "]" => Fan.algebraicRealization A
local notation "π[" H "]" => FanHom.algebraicMap (IsSubdivision.toFanHom H)
local notation "D[" A "," h "]" => Fan.boundaryIdeal A (IsComplete.nonempty_cones h)

variable {f : X ⟶ X[Φ]} {g : X ⟶ X[Ψ]}
  (b : Module.Basis (Fin 2) ℤ N)

variable [IsLocallyNoetherian X] in
/-- The intermediate fan of a factorization into ordered internal blowups and a
toric subdivision is determined by the specified map and its pole boundary.
The orders on the same boundary prime recover the same primitive ray generator
in either factorization. -/
theorem eq_of_toric_internal_factorizations (hc : Φ.IsComplete)
    (hΘ : Θ.IsRegular) (hΩ : Ω.IsRegular) (J : Θ.IsSubdivision Φ) (K : Ω.IsSubdivision Φ)
    {m n : ℕ} (r : Fin m → Θ.Ray) (s : Fin n → Ω.Ray) (c : Fin m → ℂˣ) (d : Fin n → ℂˣ) :
    letI := hc.nonempty_cones
    letI := J.nonempty_cones_of_nonempty hc.nonempty_cones
    letI := K.nonempty_cones_of_nonempty hc.nonempty_cones
    let A := Θ.internalBlowupTower b r c
    let B := Ω.internalBlowupTower b s d
    ∀ (e : A.1 ≅ X) (e' : B.1 ≅ X),
      e.hom ≫ f = A.2.toTower.toBase ≫ π[J] →
      e'.hom ≫ f = B.2.toTower.toBase ≫ π[K] →
      P.comap e.hom = A.2.boundaryι.ker →
      P.comap e'.hom = B.2.boundaryι.ker →
      Θ = Ω := by
  intro A B e e' he he' hP hP'
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Θ.cones := J.nonempty_cones_of_nonempty inferInstance
  let : Nonempty Ω.cones := K.nonempty_cones_of_nonempty inferInstance
  have := Θ.isIntegral_internalBlowupTower b r c hΘ
  have := Θ.isModification_internalBlowupTower_toBase b r c hΘ
  have : IsDominant (e.hom ≫ f) := by rw [he]; infer_instance
  have : IsDominant f := IsDominant.of_comp e.hom f
  obtain ⟨R, hR, -⟩ := exists_equiv_boundaryPrimes_of_toric_internal_factorization
    b hΘ J r c e he hP
  obtain ⟨U, hU, -⟩ := exists_equiv_boundaryPrimes_of_toric_internal_factorization
    b hΩ K s d e' he' hP'
  have hgen {t : Θ.Ray} {u : Ω.Ray} (h : R t = U u) :
      t.primitiveGenerator = u.primitiveGenerator := by
    apply b.repr.injective
    ext j
    let a := (b.coord j).toAddMonoidHom
    exact ((hR t (U u)).mp h a).symm.trans ((hU u (U u)).mp rfl a)
  apply eq_of_range_primitiveGenerator_eq b hΘ hΩ
    (J.isComplete_iff.mpr hc) (K.isComplete_iff.mpr hc)
  rw [← (R.trans U.symm).surjective.range_comp (Ray.primitiveGenerator (Phi := Ω))]
  exact congrArg Set.range (funext fun t ↦ hgen (U.apply_symm_apply (R t)).symm)

variable [X.Over S] [X.IsProjectiveOver ℂ] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [f.IsOver S] [IsModification f]

/-- When a specified logarithmic morphism already factors through a regular
toric subdivision, a single ordered internal model realizes both projections.
Both projections are the given morphisms on the whole surface, and the
boundary of the internal model is the original pole ideal. -/
theorem IsSubdivision.exists_common_toric_internal_factorization
    (H : Ψ.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
    (hfg : g ≫ π[H] = f)
    (hPole : letI := SmoothOfRelativeDimension.smooth 2 (X ↘ S)
      (D[Φ,hc]).comap f = P * ramificationIdealSheaf ℂ f) :
    ∃ (Θ : Fan i) (_ : Θ.IsRegular) (K : Θ.IsSubdivision Ψ),
      letI := (K.trans H).nonempty_cones_of_nonempty hc.nonempty_cones
      ∃ (m : ℕ) (r : Fin m → Θ.Ray) (c : Fin m → ℂˣ),
        let A := Θ.internalBlowupTower b r c
        ∃ e : A.1 ≅ X,
          e.hom ≫ g = A.2.toTower.toBase ≫ π[K] ∧
          e.hom ≫ f = A.2.toTower.toBase ≫ π[K.trans H] ∧
          P.comap e.hom = A.2.boundaryι.ker := by
  subst f
  let hc' := H.isComplete_iff.mpr hc
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Ψ.cones := hc'.nonempty_cones
  have hN : Module.finrank ℤ N = 2 :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : IsModification π[H] := H.isModification_algebraicMap hΦ hΨ hc.nonempty_cones hN
  let : IsModification g := IsModification.of_comp_right g π[H]
  let : g.IsOver S := ⟨by
    rw [Ψ.algebraicRealization_over,
      ← H.toFanHom.algebraicMap_comp_algebraicRealizationStructureMap,
      ← Category.assoc, ← Φ.algebraicRealization_over, comp_over]⟩
  have hpole' :=
    (H.comap_boundaryIdeal_eq_mul_ramificationIdealSheaf_comp_iff hΦ hΨ hc hN g P).mp hPole
  obtain ⟨Θ, hΘ, K, m, r, c, e, he, hboundary⟩ :=
    Ψ.exists_toric_internal_factorization_of_boundary_comap_eq b hΨ hc'
      (IsModification.birationalOver g) hpole'
  refine ⟨Θ, hΘ, K, m, r, c, e, he, ?_, hboundary⟩
  rw [← Category.assoc, he, Category.assoc, IsSubdivision.toFanHom_trans K H,
    FanHom.algebraicMap_comp]

/-- If a logarithmic morphism lifts regularly to a finer toric target, any
specified ordered internal model of the original morphism already refines that
target. Its existing tower, including all labels and infinitely near centers,
recovers the lift by a toric projection. -/
theorem IsSubdivision.exists_lift_of_toric_internal_factorization
    (H : Ψ.IsSubdivision Φ) (hΦ : Φ.IsRegular) (hΨ : Ψ.IsRegular) (hc : Φ.IsComplete)
    (hΘ : Θ.IsRegular) (J : Θ.IsSubdivision Φ) {m : ℕ} (r : Fin m → Θ.Ray) (c : Fin m → ℂˣ)
    (hfg : g ≫ π[H] = f)
    (hPole : letI := SmoothOfRelativeDimension.smooth 2 (X ↘ S)
      (D[Φ,hc]).comap f = P * ramificationIdealSheaf ℂ f) :
    letI := J.nonempty_cones_of_nonempty hc.nonempty_cones
    let A := Θ.internalBlowupTower b r c
    ∀ (e : A.1 ≅ X),
      e.hom ≫ f = A.2.toTower.toBase ≫ π[J] →
      P.comap e.hom = A.2.boundaryι.ker →
      ∃ K : Θ.IsSubdivision Ψ, e.hom ≫ g = A.2.toTower.toBase ≫ π[K] := by
  intro A e he hboundary
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : Nonempty Ψ.cones := H.nonempty_cones_of_nonempty inferInstance
  let : Nonempty Θ.cones := J.nonempty_cones_of_nonempty inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
  obtain ⟨Ω, hΩ, K, n, s, d, e', -, he', hboundary'⟩ :=
    H.exists_common_toric_internal_factorization b hΦ hΨ hc hfg hPole
  have h := eq_of_toric_internal_factorizations b hc hΘ hΩ J (K.trans H) r s c d
    e e' he he' hboundary hboundary'
  subst Ω
  have hN : Module.finrank ℤ N = 2 :=
    (Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)
  let : IsModification π[H] := H.isModification_algebraicMap hΦ hΨ hc.nonempty_cones hN
  let : IsModification (g ≫ π[H]) := hfg.symm ▸ ‹IsModification f›
  let : IsModification g := IsModification.of_comp_right g π[H]
  let : IsIntegral A.1 := Θ.isIntegral_internalBlowupTower b r c hΘ
  let : IsModification A.2.toTower.toBase :=
    Θ.isModification_internalBlowupTower_toBase b r c hΘ
  refine ⟨K, Scheme.Hom.eq_of_comp_eq_of_isModification π[H] ?_⟩
  rw [Category.assoc, hfg, he, Category.assoc, ← FanHom.algebraicMap_comp,
    ← IsSubdivision.toFanHom_trans K H]

end TauCeti.Toric.Fan
