/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import TauCeti.Algebra.Group.FreeAbelianCharacter

/-!
# Characters of lattice quotients in Smith coordinates

A Smith basis identifies the characters of a lattice quotient with roots of unity on the
paired basis indices and arbitrary units on the remaining indices. For a finite free
lattice, the number of free unit coordinates is the rank difference.
-/

public noncomputable section

open Multiplicative

namespace Module.Basis.SmithNormalForm

-- Use the inherited scalar action when referring to the Smith basis of a submodule.
attribute [local instance high] Submodule.module

variable {k N ι : Type*} [CommMonoid k] [AddCommGroup N] [Module ℤ N]
  {H : Submodule ℤ N} {r : ℕ}

/-- In a Smith basis, a character descends to the quotient exactly when each paired
coordinate is a root of unity of order dividing the absolute Smith coefficient. -/
theorem mem_domRestrictHom_ker_iff (snf : Basis.SmithNormalForm H ι r)
    (χ : Multiplicative N →* kˣ) :
    χ ∈ (MonoidHom.domRestrictHom H.toAddSubgroup.toSubgroup kˣ).ker ↔
      ∀ i, χ (ofAdd (snf.bM (snf.f i))) ∈ rootsOfUnity (snf.a i).natAbs k := by
  have h (i : Fin r) :
      χ (ofAdd (snf.bN i : N)) = χ (ofAdd (snf.bM (snf.f i))) ^ snf.a i := by
    rw [snf.snf, ← map_zpow, ← ofAdd_zsmul]
    exact congrArg (fun n : N ↦ χ (ofAdd n))
      (int_smul_eq_zsmul (inferInstance : Module ℤ N) _ _)
  simp only [MonoidHom.mem_ker, MonoidHom.domRestrictHom_apply, mem_rootsOfUnity,
    pow_natAbs_eq_one, ← h]
  constructor
  · intro hc i
    exact DFunLike.congr_fun hc (ofAdd (snf.bN i))
  · intro hc
    apply (MonoidHom.toAdditiveRight (α := H) (β := kˣ)).injective
    let f : H →+ Additive kˣ := (MonoidHom.toAdditiveRight (α := H) (β := kˣ))
      (χ.domRestrict H.toAddSubgroup.toSubgroup)
    let F : H →ₗ[ℤ] Additive kˣ :=
      { __ := f
        map_smul' := map_intCast_smul f ℤ ℤ }
    have hF : F = 0 := snf.bN.ext fun i ↦ congrArg Additive.ofMul (hc i)
    exact congrArg LinearMap.toAddMonoidHom hF

/-- Smith coordinates identify the quotient character group with a product of groups of
roots of unity and one copy of the unit group for each unused basis index. -/
def quotientCharactersMulEquiv (snf : Basis.SmithNormalForm H ι r) :
    (Multiplicative (N ⧸ H.toAddSubgroup) →* kˣ) ≃*
      (∀ i, rootsOfUnity (snf.a i).natAbs k) × (↥((Set.range snf.f)ᶜ : Set ι) → kˣ) := by
  classical
  let toKernel := (MonoidHom.domRestrictHomKerEquiv kˣ H.toAddSubgroup.toSubgroup).symm
  let coord : (Multiplicative N →* kˣ) ≃* (ι → kˣ) :=
    snf.bM.repr.toAddEquiv.toMultiplicative.monoidHomCongrLeft.trans
      TauCeti.freeAbelianCharEquiv
  have hcoord (χ : Multiplicative N →* kˣ) (i : ι) :
      coord χ i = χ (ofAdd (snf.bM i)) := by
    dsimp only [coord]
    rw [MulEquiv.trans_apply, TauCeti.freeAbelianCharEquiv_apply]
    exact congrArg (fun n : N ↦ χ (ofAdd n)) (snf.bM.repr_symm_single_one i)
  let φ : (MonoidHom.domRestrictHom H.toAddSubgroup.toSubgroup kˣ).ker →*
      (∀ i, rootsOfUnity (snf.a i).natAbs k) × (↥((Set.range snf.f)ᶜ : Set ι) → kˣ) :=
    { toFun χ := (fun i ↦ ⟨χ.val (ofAdd (snf.bM (snf.f i))),
        (snf.mem_domRestrictHom_ker_iff χ.val).mp χ.property i⟩,
        fun j ↦ χ.val (ofAdd (snf.bM j)))
      map_one' := rfl
      map_mul' _ _ := rfl }
  refine toKernel.trans (MulEquiv.ofBijective φ ⟨?_, ?_⟩)
  · intro χ ψ hφ
    apply Subtype.ext
    apply coord.injective
    funext j
    simp only [hcoord]
    by_cases hj : j ∈ Set.range snf.f
    · obtain ⟨i, rfl⟩ := hj
      exact congrArg (fun z ↦ (z.1 i : kˣ)) hφ
    · exact congrArg (fun z ↦ z.2 ⟨j, hj⟩) hφ
  · rintro ⟨a, b⟩
    let e := Equiv.ofInjective snf.f snf.f.injective
    let c := (Equiv.Set.sumCompl (Set.range snf.f)).symm
    let x : ι → kˣ := Sum.elim (fun i ↦ (a (e.symm i) : kˣ)) b ∘ c
    let χ := coord.symm x
    have hx (j : ι) : χ (ofAdd (snf.bM j)) = x j := by
      rw [← hcoord, MulEquiv.apply_symm_apply]
    have ha (i : Fin r) : χ (ofAdd (snf.bM (snf.f i))) = (a i : kˣ) := by
      rw [hx]
      have hi : c (snf.f i) = Sum.inl (e i) := by
        apply c.symm.injective
        simp [c, e]
      simp only [x, Function.comp_apply, hi, Sum.elim_inl]
      exact congrArg (fun j ↦ (a j : kˣ)) (e.symm_apply_apply i)
    refine ⟨⟨χ, (snf.mem_domRestrictHom_ker_iff χ).mpr fun i ↦
      ha i ▸ (a i).property⟩, Prod.ext (funext fun i ↦ Subtype.ext (ha i)) ?_⟩
    funext j
    -- The second factor uses only the basis indices outside the Smith embedding.
    change χ (ofAdd (snf.bM j)) = b j
    rw [hx]
    simp [x, c]

@[simp]
theorem quotientCharactersMulEquiv_fst_apply (snf : Basis.SmithNormalForm H ι r)
    (χ : Multiplicative (N ⧸ H.toAddSubgroup) →* kˣ) (i : Fin r) :
    ((snf.quotientCharactersMulEquiv χ).1 i : kˣ) =
      χ (ofAdd (snf.bM (snf.f i) : N ⧸ H.toAddSubgroup)) := (rfl)

@[simp]
theorem quotientCharactersMulEquiv_snd_apply (snf : Basis.SmithNormalForm H ι r)
    (χ : Multiplicative (N ⧸ H.toAddSubgroup) →* kˣ) (j : ↥((Set.range snf.f)ᶜ : Set ι)) :
    (snf.quotientCharactersMulEquiv χ).2 j =
      χ (ofAdd (snf.bM j : N ⧸ H.toAddSubgroup)) := (rfl)

end Module.Basis.SmithNormalForm

namespace QPainleve.CharacterTorus

open Module

variable {N : Type*} [AddCommGroup N] [Module ℤ N]

attribute [local instance high] Submodule.module

/-- The quotient character group of a finite free lattice has one free unit coordinate
per missing rank and one root-of-unity factor per Smith coefficient of the sublattice. -/
theorem exists_quotientCharactersMulEquiv (k : Type*) [CommMonoid k]
    [Free ℤ N] [Module.Finite ℤ N] (H : Submodule ℤ N) :
    ∃ d : Fin (finrank ℤ H) → ℕ, (∀ i, 0 < d i) ∧
      Nonempty ((Multiplicative (N ⧸ H.toAddSubgroup) →* kˣ) ≃*
        (∀ i, rootsOfUnity (d i) k) × (Fin (finrank ℤ N - finrank ℤ H) → kˣ)) := by
  classical
  obtain ⟨r, snf⟩ := H.smithNormalForm (Free.chooseBasis ℤ N)
  have hr : finrank ℤ H = r := by simp [finrank_eq_card_basis snf.bN]
  have hc : Fintype.card ↥((Set.range snf.f)ᶜ) = finrank ℤ N - r := by
    rw [Fintype.card_compl_set, Fintype.card_range, ← finrank_eq_card_basis snf.bM,
      Fintype.card_fin]
  rw [hr]
  refine ⟨fun i ↦ (snf.a i).natAbs, fun i ↦ ?_, ⟨?_⟩⟩
  · apply Int.natAbs_pos.mpr
    intro h
    apply snf.bN.ne_zero i
    apply Subtype.coe_injective
    simp [snf.snf, h]
  · let e := Fintype.equivFinOfCardEq hc
    exact snf.quotientCharactersMulEquiv.trans <|
      MulEquiv.prodCongr (MulEquiv.refl _)
        { toEquiv := Equiv.arrowCongr e (Equiv.refl kˣ)
          map_mul' _ _ := rfl }

end QPainleve.CharacterTorus
