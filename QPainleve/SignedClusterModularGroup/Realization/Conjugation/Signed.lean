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

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

variable {n : ℕ} [NeZero n] {L₀ L₁ : Type} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : BilinForm ℤ L₀} {B₁ : BilinForm ℤ L₁} {d₀ : ZMod n → L₀} {d₁ : ZMod n → L₁}

local notation "S" => Spec (CommRingCat.of k₀)
local notation "X[" coeff "," r "]" => scheme coeff (Fin r →₀ ℤ)
local notation "Maps[" E "]" => (SignedClusterModularGroup k₀ E)ᵐᵒᵖ
local notation "eval[" E "," v "]" => op (signedClusterModularGroupMap k₀ E (End.of v))

variable {r : ℕ} {E₀ E₁ : SkewExchangeMatrix (Fin r)}
  {T₀ T₁ : Over (Spec (.of k₀))} [Nonempty T₀.left] [Smooth T₀.hom] [PreirreducibleSpace T₀.left]
  [Nonempty T₁.left] [Smooth T₁.hom]
  {P₀ : Point T₀ → MarkedSurface k₀ n B₀ X[k₀,r]} {P₁ : Point T₁ → MarkedSurface k₀ n B₁ X[k₀,r]}
  {C : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
  {w : Word E₀ E₁} (R : GeometricRealization P₀ P₁ C (w.xRationalMap k₀))
  {h₀ : ∀ c, (P₀ c).pair.hom.left.ker.IsEffectiveCartier}
  {h₁ : ∀ c, (P₁ c).pair.hom.left.ker.IsEffectiveCartier}
  (hd₀ : ∀ c j, (P₀ c).boundaryClass (h₀ c) j = d₀ j)
  (hd₁ : ∀ c j, (P₁ c).boundaryClass (h₁ c) j = d₁ j)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [hΦ₀ : Nonempty Φ.cones]
  {b : Module.Basis (Fin 2) ℤ N} {s : Fin r → Φ.Ray} {hΦ : Φ.IsRegular}
  {m : ℕ} [NeZero m] [PrestableFamily ((Φ.toricBoundaryIdeal k₀ hΦ₀).subscheme ↘ Spec (.of k₀))]
  {γ : Type*} {p : γ → ((Φ.toricBoundaryIdeal k₀ hΦ₀).subscheme ↘ Spec (.of k₀)).smoothLocus}
  {T : NodalCycleNumbering p m} {origin : ZMod m}
  {ι : L₁ →ₗ[ℤ] Additive (LineBundleClass (Φ.finiteFanScheme k₀)) × (Fin r → ℤ)}
  {centers : Point T₁ → Multiplicative (Fin r → ℤ) →* k₀ˣ}

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
      ∃ A : GeometricRealization P₀ P₀ D (v.xRationalMap k₀),
        ρ₀ eval[E₀,v] = A.toSignedBoundaryIsometry d₀ h₀ hd₀)
    (hreal₁ : ∀ v : Word E₁ E₁, ∃ (J : T₁.left.PartialMap T₁.left)
      (hJ : IsDominant J.hom) (hJO : J.IsOver T₁.hom T₁.hom),
      letI := hJ
      letI := hJO
      ∃ B : GeometricRealization P₁ P₁ J (v.xRationalMap k₀),
        Models[J] ∧ ρ₁ eval[E₁,v] = B.toSignedBoundaryIsometry d₁ h₁ hd₁) :
    ρ₁.comp (MulEquiv.op (signedClusterModularGroupCongr k₀ w)).toMonoidHom =
      (R.signedBoundaryIsometryGroupCongr hd₀ hd₁).toMonoidHom.comp ρ₀ := by
  apply MonoidHom.ext
  intro g
  obtain ⟨loop, hloop⟩ := signedClusterModularGroupMap_surjective k₀ E₀ g.unop
  let v : Word E₀ E₀ := loop.asHom
  let u : Word E₁ E₁ := (w.reverse.comp v).comp w
  obtain ⟨D, hD, hDO, A, hA⟩ := hreal₀ v
  obtain ⟨J, hJ, hJO, B, hmodel, hB⟩ := hreal₁ u
  let := hD
  let := hDO
  let := hJ
  let := hJO
  have hcomp := w.xRationalMap_comp_eq_of_xPullback_eq_conj k₀ (v := v) (u := u) rfl
  obtain ⟨hpic, hsign⟩ := R.picard_conjugation_of_comp_xMap_eq A B hcomp hc hι hindex hC hmodel
  have hg : g = eval[E₀,v] := op_unop g ▸ congrArg op hloop.symm
  have hcongr : MulEquiv.op (signedClusterModularGroupCongr k₀ w) (eval[E₀,v]) = eval[E₁,u] := by
    simp only [MulEquiv.op_apply_apply, Function.comp_apply, unop_op,
      signedClusterModularGroupCongr_map]
    rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hg, hcongr, hA, hB]
  apply Subtype.ext
  rw [coe_toSignedBoundaryIsometry, coe_signedBoundaryIsometryGroupCongr,
    coe_toSignedBoundaryIsometry]
  exact Prod.ext hpic hsign

end QPainleve.SignedClusterModularGroup.GeometricRealization
