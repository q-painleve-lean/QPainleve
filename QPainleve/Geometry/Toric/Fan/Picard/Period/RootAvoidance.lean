/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.BoundaryCharacter
public import QPainleve.Geometry.Toric.Fan.Picard.Period.Surjectivity

import QPainleve.AlgebraicGeometry.Curves.Node.Period.Roots
import QPainleve.Geometry.Toric.BaseChange.Fan

/-!
# Center choices with root-avoiding periods

An injective character on the boundary orthogonal of a reference surface gives two
actual center choices in a fixed toric presentation, with periods related by a charge
action and an orientation sign. Distinct labels give centers with disjoint supports.
When an ordered model is contracted to a numbered nodal pair with the same period,
injectivity rules out internal curves on that pair.

See [Gross, Hacking and Keel, Proposition 2.9](https://arxiv.org/html/1211.6367v5#S2)
for construction of a toric model from a period.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative TopologicalSpace
open QPainleve QPainleve.BlowupTower TauCeti TauCeti.AlgebraicGeometry LineBundleClass
open Scheme (NodalCycleNumbering IdealSheafData)

namespace TauCeti.Toric.Fan

variable (F : Type) [Field F] [IsAlgClosed F]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [Nonempty Φ.cones] {n : ℕ}
  (hΦ : Φ.IsRegular) (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray)

local notation "ChargeKernel" => LinearMap.ker (rayChargeMap s)
local notation "C" => IdealSheafData.subscheme (Φ.toricBoundaryIdeal F inferInstance)

variable [(Φ.finiteFanScheme F).IsProjectiveOver F]
  {c : Fin n → Fˣ} {X Y : Scheme} [X.Over (Spec (.of F))] [X.IsProjectiveOver F]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of F))]
  {D : X.IdealSheafData} {d : ℕ} {T : BlowupTower X d Y}
  (hT : IsNodalBoundaryTower D (X ↘ Spec (.of F)) (𝟙 X) T)
  (e : Y ≅ (alongBoundary (Φ.toricBoundaryIdeal F inferInstance).subschemeι
    (fun j ↦ (s j).internalCenter F b (c j))).1)
  (he : e.inv ≫ T.toBase ≫ (X ↘ Spec (.of F)) =
    (alongBoundary (Φ.toricBoundaryIdeal F inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter F b (c j))).2.toTower.toBase ≫
      ((Φ.finiteFanScheme F) ↘ Spec (.of F)))
  (hD : ((D.comap T.toBase).comap e.inv).support =
    (alongBoundary (Φ.toricBoundaryIdeal F inferInstance).subschemeι
      (fun j ↦ (s j).internalCenter F b (c j))).2.boundaryι.ker.support)
  (hCartier : D.IsEffectiveCartier)

variable [PrestableFamily ((Φ.toricBoundaryIdeal F inferInstance).subscheme ↘ Spec (.of F))]
  {α : Type*}
  {p : α → ((Φ.toricBoundaryIdeal F inferInstance).subscheme ↘ Spec (.of F)).smoothLocus}
  {a : ℕ} [NeZero a]
  (A : NodalCycleNumbering p a)

local notation "period" => orderedBoundaryPeriod F hΦ b s A
local notation "coord" => markedBoundaryChargeEquiv F hΦ b s hT e he hD
local notation "centerSupport[" c "," j "]" =>
  (SetLike.coe (IdealSheafData.support (Subtype.val (Ray.internalCenter F b (s j) (c j)))) : Set C)
local notation "δ" => (Additive.ofMul (LineBundleClass.mk hCartier.toInvertibleSheaf)⁻¹)
local notation "B" => Chow.intersectionBilinForm F X
local notation "toricForm" => LinearMap.BilinForm.prod
  (Chow.intersectionBilinForm F (Fan.finiteFanScheme F Φ))
  (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ)))

section RationalReference

variable [rational : Scheme.IsRationalOver (X ↘ Spec (.of F))]

/-- For a primitive nef square-zero boundary on a rational reference surface, choose
two ordered toric models with injective periods related by a specified charge action
and orientation sign. The first period takes value `1/2` on the reference boundary
class, and both periods avoid one on all translates of square `-2` classes by that
class. In each model the labeled centers have disjoint supports on the toric boundary. -/
theorem exists_root_avoiding_ordered_boundary_periods [CharZero F]
    (r : ZMod a ≃ Φ.Ray)
    (hr : ∀ j, (C).dualGraphVertexEquiv p (A.vertex j) =
      Φ.boundaryNormalizationComponentEquiv F hΦ (r j))
    (hdet : ∀ j, b.detDualEquiv (r j).primitiveGenerator (r (j + 1)).primitiveGenerator = 1)
    (hnodes : ∀ j, ∃ σ : Φ.cones, (r j).toCone ≤ σ ∧ (r (j + 1)).toCone ≤ σ ∧
      (Φ.toricBoundaryIdeal F inferInstance).subschemeι ((C).dualGraphEdgeEquiv p (A.edge j)).val =
        (Φ.distinguishedSection (R := F) σ) (IsLocalRing.closedPoint F))
    (hprim : IsPrimitive δ) (hnef : (δ).toMul.IsNef F (X ↘ Spec (.of F)))
    (hsq : let : Smooth (X ↘ Spec (.of F)) := SmoothOfRelativeDimension.smooth 2 _
      let : IsIntegral X := rational.isIntegral_of_smooth
      B δ δ = 0)
    (g : ChargeKernel ≃ₗ[ℤ] ChargeKernel) (η : ℤˣ) :
    let : Smooth (X ↘ Spec (.of F)) := SmoothOfRelativeDimension.smooth 2 _
    let : IsIntegral X := rational.isIntegral_of_smooth
    let : LinearMap.IsPerfPair B := Chow.isPerfPair_intersectionBilinForm_of_isRationalOver F X
    let : SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme F) ↘ Spec (.of F)) := by
      have hrank : Module.finrank ℤ N = 2 := by simpa using Module.finrank_eq_card_basis b
      rw [finiteFanScheme_over]
      exact hrank ▸ Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec F hΦ
    let : LinearMap.IsPerfPair toricForm :=
      isPerfPair_internal_markedForm F hΦ (by simpa using Module.finrank_eq_card_basis b) s
        (fun j ↦ (b.detDualEquiv (s j).primitiveGenerator).toAddMonoidHom)
        (fun j ↦ b.detDualEquiv_self (s j).primitiveGenerator)
        (fun j ↦ (s j).surjective_detCharacter b) c
        (fun j ↦ (s j).internalCenter F b (c j))
        (fun j ↦ (s j).internalCenter_val F b (c j)) hT e he
    ∃ (v : D.boundaryOrthogonal F) (c₀ c₁ : Fin n → Fˣ), v.val = δ ∧
      Function.Injective (period c₀) ∧ Function.Injective (period c₁) ∧
      (period c₀ (ofAdd (coord v)) : F) = (2 : F)⁻¹ ∧
      (∀ x : ChargeKernel, period c₁ (ofAdd x) = period c₀ (ofAdd (g x)) ^ (η : ℤ)) ∧
      (Pairwise fun j l ↦ Disjoint centerSupport[c₀,j] centerSupport[c₀,l]) ∧
      (Pairwise fun j l ↦ Disjoint centerSupport[c₁,j] centerSupport[c₁,l]) ∧
      ∀ (x : D.boundaryOrthogonal F), B x.val x.val = -2 → ∀ m : ℤ,
        period c₀ (ofAdd (coord (x + m • v))) ≠ 1 ∧
        period c₁ (ofAdd (coord (x + m • v))) ≠ 1 := by
  intro _ _ _ _ _
  obtain ⟨v, χ, hv, hχ, hval, hroot⟩ :=
    hCartier.exists_root_avoiding_boundary_character hprim hnef hsq
  let q := (coord).symm.toAddEquiv.toMultiplicative
  let χ₀ := χ.comp q.toMonoidHom
  let χ₁ := (zpowGroupHom (η : ℤ)).comp (χ₀.comp g.toAddEquiv.toMultiplicative.toMonoidHom)
  obtain ⟨c₀, hc₀⟩ := orderedBoundaryPeriod_surjective F hΦ b s A r hr hdet hnodes χ₀
  obtain ⟨c₁, hc₁⟩ := orderedBoundaryPeriod_surjective F hΦ b s A r hr hdet hnodes χ₁
  have hinj₀ : Function.Injective χ₀ := hχ.comp q.injective
  have hinj₁ : Function.Injective χ₁ := by
    have hpow : Function.Injective (zpowGroupHom (α := Fˣ) (η : ℤ)) := by
      apply Function.LeftInverse.injective (g := zpowGroupHom ((η⁻¹ : ℤˣ) : ℤ))
      intro x
      simp [zpowGroupHom_apply, ← zpow_mul, ← Units.val_mul]
    exact hpow.comp (hinj₀.comp g.toAddEquiv.toMultiplicative.injective)
  have h₀ : Function.Injective (period c₀) := hc₀ ▸ hinj₀
  have h₁ : Function.Injective (period c₁) := hc₁ ▸ hinj₁
  refine ⟨v, c₀, c₁, hv, h₀, h₁, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hc₀, χ₀, q] using hval
  · intro x
    rw [hc₀, hc₁]
    rfl
  · exact pairwise_disjoint_internalCenters_of_orderedBoundaryPeriod_injective F hΦ b s A h₀
  · exact pairwise_disjoint_internalCenters_of_orderedBoundaryPeriod_injective F hΦ b s A h₁
  · intro x hx m
    have h : period c₀ (ofAdd (coord (x + m • v))) ≠ 1 := by
      simpa [hc₀, χ₀, q] using hroot x hx m
    refine ⟨h, fun hz ↦ h ?_⟩
    rw [h₁ (hz.trans ((period c₁).map_one).symm), map_one]

end RationalReference

variable [IsIntegral X] [LinearMap.IsPerfPair (Chow.intersectionBilinForm F X)]
  [SmoothOfRelativeDimension 2 ((Φ.finiteFanScheme F) ↘ Spec (.of F))]
  [LinearMap.IsPerfPair
    ((Chow.intersectionBilinForm F (Φ.finiteFanScheme F)).prod
      (-(dotProductBilin ℤ ℤ : LinearMap.BilinForm ℤ (Fin n → ℤ))))]
  [PrestableFamily (D.subscheme ↘ Spec (.of F))]
  (hgenus : ∀ v : irreducibleComponents (D.subscheme.singularLocus F).blowup,
    (D.subscheme.blowupComponent (K := F) v).toScheme.genus F = 0)
  {β : Type*} {q : β → (D.subscheme ↘ Spec (.of F)).smoothLocus} {k : ℕ} [NeZero k]
  (A₀ : NodalCycleNumbering q k)

/-- If the marked period of a contraction agrees with its injective ordered period,
every prime curve on the contracted surface meets the boundary. -/
theorem not_disjoint_primeDivisor_of_orderedBoundaryPeriod_injective
    (hperiod : markedBoundaryPeriod F hΦ b s hT e he hD hCartier hgenus A₀ = period c)
    (hinj : Function.Injective (period c)) (z : CodimensionOnePoint X) :
    ¬Disjoint (closure {(z : X)}) (D.support : Set X) := by
  apply hCartier.not_disjoint_primeDivisor_of_boundaryPeriod_injective hgenus A₀.endpoint_eq _ z
  exact (markedBoundaryPeriod_injective_iff F hΦ b s hT e he hD hCartier hgenus A₀).mp
    (hperiod.symm ▸ hinj)

end TauCeti.Toric.Fan
