/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import QPainleve.Geometry.Toric.Fan.Boundary.Branches
public import QPainleve.Geometry.Toric.Fan.TorusAction.Automorphism

import QPainleve.Geometry.Toric.Fan.Boundary.Automorphism

/-!
# Torus translations on the branches of the boundary

A torus translation fixes the individual branches of the reduced boundary of a
complete regular toric surface. Its restriction fixes each node as the intersection
of two ray divisors. Over a node, the normalized ray component distinguishes its
branch. This supplies the branch comparison for the toric automorphisms in
[Gross, Hacking and Keel, Proposition 2.6](https://arxiv.org/html/1211.6367v5#S2).
-/

public section

open AlgebraicGeometry CategoryTheory DihedralGroup Multiplicative
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData QPainleve.BlowupTower

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} [h₀ : Nonempty Φ.cones]

local notation "D" => Φ.boundaryIdeal h₀
local notation "C" => Scheme.IdealSheafData.subscheme D
local notation "base" => Spec (CommRingCat.of ℂ)
variable [PrestableFamily ((Φ.boundaryIdeal h₀).subscheme ↘ Spec (.of ℂ))]

local notation "Chars" => (Multiplicative (N →+ ℤ) →* ℂˣ)

/-- Every torus translation acts as the identity on the actual branch scheme of the
reduced boundary of a complete regular toric surface. -/
theorem branchSchemeIso_boundaryTranslation (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hdim : Module.finrank ℤ N = 2) (χ : Chars) :
    (boundaryTranslation (Φ := Φ) χ).branchSchemeIso (R := ℂ) =
      Iso.refl (Scheme.branchScheme ℂ C) :=
  branchSchemeIso_eq_refl_of_comap_rayBoundaryIdeal_eq hΦ (Φ.torusTranslation χ)
    (boundaryTranslation χ) (boundaryTranslation_hom_subschemeι χ)
    (Φ.comap_rayBoundaryIdeal_torusTranslation_hom hΦ χ) hc hdim

/-- Torus translation induces the identity on any numbering of the toric boundary cycle. -/
theorem boundaryCycleAction_boundaryTranslation
    (hΦ : Φ.IsRegular)
    (hc : Φ.IsComplete) (hdim : Module.finrank ℤ N = 2)
    {m : ℕ} [NeZero m] {γ : Type*} {a : γ → (C ↘ base).smoothLocus}
    (T : Scheme.NodalCycleNumbering a m) (χ : Chars) :
    (boundaryTranslation (Φ := Φ) χ).boundaryCycleAction T T = 1 := by
  apply cycleBranchPerm_injective m
  apply Equiv.ext
  rintro ⟨j, l⟩
  apply T.branch.injective
  rw [map_one, Equiv.Perm.one_apply, Iso.branch_boundaryCycleAction,
    branchSchemeIso_boundaryTranslation hΦ hc hdim]
  rfl

variable {n : ℕ} (b : Module.Basis (Fin 2) ℤ N) (s : Fin n → Φ.Ray) {c c' : Fin n → ℂˣ}

local notation "Y" a:arg => Sigma.fst (internalBlowupTower b s a)
local notation "T" a:arg => WithBoundary.toTower (Sigma.snd (internalBlowupTower b s a))
local notation "ι" a:arg => WithBoundary.boundaryι (Sigma.snd (internalBlowupTower b s a))

/-- A torus translation lifted through ordered internal blowups acts trivially on the
branches under the canonical identifications of the two strict boundaries with the
original toric boundary. This holds for repeated and infinitely near centers. -/
theorem branchSchemeIso_eq_refl_of_isLift_internalBlowupTower_torusTranslation
    (hreg : Φ.IsRegular) (hc : Φ.IsComplete) (χ : Chars) {g : Y c ≅ Y c'}
    (hg : IsLift (Φ.torusTranslation χ) (T c) (T c') g)
    {a : C ≅ C} [a.hom.IsOver base] (ha : ι c ≫ g.hom = a.hom ≫ ι c') :
    a.branchSchemeIso (R := ℂ) = Iso.refl (Scheme.branchScheme ℂ C) := by
  have h := boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation b s c c' χ hg
  have hEq : a = boundaryTranslation χ :=
    Iso.ext ((cancel_mono (ι c')).mp (ha.symm.trans h))
  subst a
  exact branchSchemeIso_boundaryTranslation hreg hc
    ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) χ

/-- A Picard-trivial automorphism fixing the strict boundary divisors of an
ordered internal model restricts to a unique boundary automorphism over the base
field, and its induced isomorphism of the branch scheme is the identity. -/
theorem existsUnique_boundaryIso_of_internalBlowupPicardBoundaryAut
    (hreg : Φ.IsRegular) (hc : Φ.IsComplete)
    (g : internalBlowupPicardBoundaryAut b s c hreg) :
    ∃! a : C ≅ C, ∃ ha : a.hom.IsOver base,
      ι c ≫ (g.val.asIso).hom = a.hom ≫ ι c ∧
        (letI := ha; a.branchSchemeIso (R := ℂ) = Iso.refl (Scheme.branchScheme ℂ C)) := by
  obtain ⟨z, rfl⟩ := (internalBlowupPicardBoundaryAutMulEquiv b s c hreg hc).surjective g
  have h := internalBlowupPicardBoundaryAutMulEquiv_isLift b s c hreg hc z
  have hcomm := boundaryι_comp_of_isLift_internalBlowupTower_torusTranslation b s c c _ h
  refine ⟨_, ⟨inferInstance, hcomm, ?_⟩, ?_⟩
  · exact branchSchemeIso_eq_refl_of_isLift_internalBlowupTower_torusTranslation
      b s hreg hc _ h hcomm
  · rintro a ⟨_, ha, -⟩
    exact Iso.ext ((cancel_mono (ι c)).mp (ha.symm.trans hcomm))

end TauCeti.Toric.Fan
