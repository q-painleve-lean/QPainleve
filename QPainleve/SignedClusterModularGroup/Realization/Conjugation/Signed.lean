/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Realization.Conjugation.Basic

/-!
# Change of base seed for signed Picard actions

A connecting word transports signed loops by conjugation. Their marked Picard
pullbacks conjugate by the pullback of the connecting realization, and their
orientation signs agree even when the branch action is invisible on the set
of components. The comparison applies to the actions characterized by
`GeometricRealization.existsUnique_signedPicardHom_of_realizations`.
-/

public section

open AlgebraicGeometry CategoryTheory MulOpposite Multiplicative
open QPainleve.CharacterTorus QPainleve.Cluster
open TauCeti.AlgebraicGeometry TauCeti.Toric
open LinearMap (BilinForm)
open Scheme

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

variable {n : ℕ} [NeZero n] {L₀ L₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : BilinForm ℤ L₀} {B₁ : BilinForm ℤ L₁} {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "X[" r "]" => scheme ℂ (Fin r →₀ ℤ)
local notation "Maps[" E "]" => (SignedClusterModularGroup ℂ E)ᵐᵒᵖ
local notation "eval[" E "," v "]" => op (signedClusterModularGroupMap ℂ E (End.of v))

variable {r : ℕ} {E₀ E₁ : SkewExchangeMatrix (Fin r)}
  {T₀ T₁ : Over S} [Nonempty T₀.left] [Smooth T₀.hom] [PreirreducibleSpace T₀.left]
  [Nonempty T₁.left] [Smooth T₁.hom]
  {P₀ : Point T₀ → MarkedSurface ℂ n B₀ X[r]} {P₁ : Point T₁ → MarkedSurface ℂ n B₁ X[r]}
  {C : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
  {w : Word E₀ E₁} (R : GeometricRealization P₀ P₁ C (w.xRationalMap ℂ))
  {h₀ : ∀ c, (P₀ c).pair.hom.left.ker.IsEffectiveCartier}
  {h₁ : ∀ c, (P₁ c).pair.hom.left.ker.IsEffectiveCartier}
  (hd₀ : ∀ c j, (P₀ c).boundaryClass (h₀ c) j = d₀ j)
  (hd₁ : ∀ c j, (P₁ c).boundaryClass (h₁ c) j = d₁ j)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  {m : ℕ} [NeZero m] [PrestableFamily ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S)]
  {γ : Type*} {p : γ → ((Φ.boundaryIdeal hΦ₀).subscheme ↘ S).smoothLocus}
  {T : NodalCycleNumbering p m} {origin : ZMod m}
  {ι : L₁ →ₗ[ℤ] Additive (LineBundleClass Φ.algebraicRealization) × (Fin r → ℤ)}
  {centers : Point T₁ → Multiplicative (Fin r → ℤ) →* ℂˣ}

local notation "Models[" D "]" =>
  HasToricTargetModels (b := b) (s := s) (hΦ := hΦ) (T := T) (origin := origin)
    (ι := ι) (P₁ := P₁) centers D

/-- A realized connecting word intertwines the two descended signed Picard
homomorphisms. Each homomorphism is evaluated via marked loop realizations at
its own seed. The connecting word can have either orientation, and the signed
comparison includes boundaries with one or two components. -/
theorem signedPicardHom_base_change
    (hc : Φ.IsComplete) (hι : Function.Injective ι)
    (hindex : (Fan.rayChargeMap s).range.toAddSubgroup.index ≠ 0) (hC : Models[C])
    (ρ₀ : Maps[E₀] →* signedBoundaryIsometryGroup B₀ d₀)
    (ρ₁ : Maps[E₁] →* signedBoundaryIsometryGroup B₁ d₁)
    (hreal₀ : ∀ v : Word E₀ E₀, ∃ (D : T₀.left.PartialMap T₀.left)
      (hD : IsDominant D.hom) (hDO : D.IsOver T₀.hom T₀.hom),
      letI := hD
      letI := hDO
      ∃ A : GeometricRealization P₀ P₀ D (v.xRationalMap ℂ),
        ρ₀ eval[E₀,v] = A.toSignedBoundaryIsometry d₀ h₀ hd₀)
    (hreal₁ : ∀ v : Word E₁ E₁, ∃ (J : T₁.left.PartialMap T₁.left)
      (hJ : IsDominant J.hom) (hJO : J.IsOver T₁.hom T₁.hom),
      letI := hJ
      letI := hJO
      ∃ B : GeometricRealization P₁ P₁ J (v.xRationalMap ℂ),
        Models[J] ∧ ρ₁ eval[E₁,v] = B.toSignedBoundaryIsometry d₁ h₁ hd₁) :
    ρ₁.comp (MulEquiv.op (signedClusterModularGroupCongr ℂ w)).toMonoidHom =
      (R.signedBoundaryIsometryGroupCongr hd₀ hd₁).toMonoidHom.comp ρ₀ := by
  apply MonoidHom.ext
  intro g
  obtain ⟨loop, hloop⟩ := signedClusterModularGroupMap_surjective ℂ E₀ g.unop
  let v : Word E₀ E₀ := loop.asHom
  let u : Word E₁ E₁ := (w.reverse.comp v).comp w
  obtain ⟨D, hD, hDO, A, hA⟩ := hreal₀ v
  obtain ⟨J, hJ, hJO, B, hmodel, hB⟩ := hreal₁ u
  let := hD
  let := hDO
  let := hJ
  let := hJO
  have hcomp : (w.xRationalMap ℂ).comp (u.xRationalMap ℂ) =
      (v.xRationalMap ℂ).comp (w.xRationalMap ℂ) := by
    have h := (Quiver.Path.xRationalMap_eq_iff ℂ (w.comp u) (v.comp w)).mpr (by
      simp only [u, Quiver.Path.xPullback_comp, Quiver.Path.xPullback_reverse]
      group)
    simpa only [Quiver.Path.xRationalMap_comp] using h
  obtain ⟨hpic, hsign⟩ := R.picard_conjugation_of_comp_xMap_eq A B hcomp hc hι hindex hC hmodel
  rw [← op_unop g, ← hloop]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  -- Evaluate the opposite equivalence on a point-map group element.
  change ρ₁ (op (signedClusterModularGroupCongr ℂ w
    (signedClusterModularGroupMap ℂ E₀ loop))) = _
  rw [signedClusterModularGroupCongr_map]
  -- Use the paths named above to apply their realization formulas.
  change ρ₁ eval[E₁,u] = _
  rw [hA, hB]
  apply Subtype.ext
  rw [coe_toSignedBoundaryIsometry, coe_signedBoundaryIsometryGroupCongr,
    coe_toSignedBoundaryIsometry]
  refine Prod.ext ?_ hsign
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hInv : R.picard.symm.symm = R.picard := rfl
  simpa only [BilinForm.IsometryEquiv.isometryGroupCongr_apply_apply, hInv,
    BilinForm.coe_isometryGroupEquivIsometryEquiv_symm] using hpic x

end QPainleve.SignedClusterModularGroup.GeometricRealization
