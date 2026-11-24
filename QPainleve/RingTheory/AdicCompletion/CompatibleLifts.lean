/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Artinian.Defs

import QPainleve.Algebra.Category.ModuleCat.Tower.Artinian
import TauCeti.Algebra.Category.ModuleCat.Tower.Reduction

/-!
# Lifting compatible families to an adic completion

Levelwise quotients of the rings `R ⧸ I ^ (n + 1)` receive every compatible family
from the `I`-adic completion when the truncations are Artinian `R`-modules.
In particular this applies to powers of the maximal ideal of a Noetherian local ring.
-/

public section

open CategoryTheory Opposite TauCeti.ModuleTower

namespace AdicCompletion

universe u

variable {R : Type u} [CommRing R] (I : Ideal R)

private noncomputable def reductionTermEquiv (n : ℕ) :
    (reduction I R).obj (op n) ≃ₗ[R] R ⧸ I ^ (n + 1) :=
  (quotientsObjEquiv _ _ n).trans
    (Ideal.quotientEquivAlgOfEq R (Ideal.mul_top (I ^ (n + 1)))).toLinearEquiv

private theorem reductionTermEquiv_reductionπ (n : ℕ) (r : R) :
    reductionTermEquiv I n (reductionπ I R n r) = Ideal.Quotient.mk (I ^ (n + 1)) r := by
  rw [reductionTermEquiv, LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply]
  have hπ : reductionπ I R n = quotientsπ _ (I.pow_succ_smul_top_antitone R) n := rfl
  rw [hπ, quotientsObjEquiv_quotientsπ]
  rfl

private theorem reductionTermEquiv_limπ (x : (reduction I R).lim) (n : ℕ) :
    reductionTermEquiv I n ((reduction I R).limπ n x) =
      evalₐ I (n + 1) (limReductionEquiv I R x) := by
  let y := limReductionEquiv I R x
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I (n + 1) y)
  have hval : y.val (n + 1) = Submodule.Quotient.mk r := by
    rw [← eval_apply, ← factor_evalₐ_eq_eval I y (Ideal.mul_top _).ge, ← hr]
    rfl
  have hπ := limπ_limReductionEquiv_symm_apply I R hval
  have hy : (limReductionEquiv I R).symm y = x := (limReductionEquiv I R).symm_apply_apply x
  rw [hy] at hπ
  rw [hπ, reductionTermEquiv_reductionπ, hr]

private theorem reduction_naturality {T : TauCeti.ModuleTower R}
    (f : ∀ n : ℕ, (reduction I R).obj (op n) →ₗ[R] T.obj (op n)) (n : ℕ)
    (h : ∀ r : R, f n (reductionπ I R n r) =
      T.transition n (f (n + 1) (reductionπ I R (n + 1) r))) :
    (reduction I R).map (homOfLE (Nat.le_succ n)).op ≫ ModuleCat.ofHom (f n) =
      ModuleCat.ofHom (f (n + 1)) ≫ T.map (homOfLE (Nat.le_succ n)).op := by
  apply ModuleCat.hom_ext
  apply quotients_hom_ext _ _
  apply LinearMap.ext
  intro r
  simpa only [LinearMap.comp_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    ← transition_def, transition_quotientsπ] using h r

/-- Every compatible family in a tower of quotients of `R ⧸ I ^ (n + 1)` lifts
to the `I`-adic completion, provided the truncations are Artinian over `R`.
The level maps `f` must commute with the transitions `t`. -/
theorem exists_evalₐ_lift_of_surjective {B : ℕ → Type u} [∀ n, CommRing (B n)]
    (t : ∀ n, B (n + 1) →+* B n) (f : ∀ n, R ⧸ I ^ (n + 1) →+* B n)
    (ht : ∀ n r, t n (f (n + 1) (Ideal.Quotient.mk _ r)) = f n (Ideal.Quotient.mk _ r))
    (hf : ∀ n, Function.Surjective (f n)) [∀ n : ℕ, IsArtinian R (R ⧸ I ^ (n + 1))]
    (b : ∀ n, B n) (hb : ∀ n, t n (b (n + 1)) = b n) :
    ∃ x : AdicCompletion I R, ∀ n, f n (evalₐ I (n + 1) x) = b n := by
  let (n : ℕ) : Algebra R (B n) := ((f n).comp (Ideal.Quotient.mk _)).toAlgebra
  let tₗ (n : ℕ) : B (n + 1) →ₗ[R] B n :=
    ({ toRingHom := t n, commutes' := ht n } : B (n + 1) →ₐ[R] B n).toLinearMap
  let T : TauCeti.ModuleTower R := Functor.ofOpSequence (X := fun n ↦ ModuleCat.of R (B n))
    (fun n ↦ ModuleCat.ofHom (tₗ n))
  have hT (n : ℕ) : T.transition n = tₗ n := by
    simp [T, transition_def]
    rfl
  let fₗ (n : ℕ) : (reduction I R).obj (op n) →ₗ[R] B n :=
    ({ toRingHom := f n, commutes' := fun _ ↦ rfl } : R ⧸ I ^ (n + 1) →ₐ[R] B n).toLinearMap ∘ₗ
      (reductionTermEquiv I n).toLinearMap
  have hfₗ (n : ℕ) (x) : fₗ n x = f n (reductionTermEquiv I n x) := rfl
  have hq (j : ℕ) (r : R) : fₗ j (reductionπ I R j r) = f j (Ideal.Quotient.mk _ r) :=
    (hfₗ j _).trans (congrArg (f j) (reductionTermEquiv_reductionπ I j r))
  let φ : reduction I R ⟶ T := NatTrans.ofOpSequence
    (fun n ↦ ModuleCat.ofHom (fₗ n)) fun n ↦ reduction_naturality I (T := T) fₗ n fun r ↦ by
      let x := fₗ (n + 1) (reductionπ I R (n + 1) r)
      have hleft := (hq n r).trans (ht n r).symm
      have hright := congrArg (t n) (hq (n + 1) r).symm
      exact hleft.trans (hright.trans (LinearMap.congr_fun (hT n) x).symm)
  let (n : ℕ) : IsArtinian R ((reduction I R).obj (op n)) :=
    (reductionTermEquiv I n).isArtinian_iff.mpr inferInstance
  let y : T.lim := ⟨b, T.mem_lim.mpr fun n ↦ by rw [hT]; exact hb n⟩
  have hφ (n : ℕ) : Function.Surjective (φ.app (op n)).hom :=
    (hf n).comp (reductionTermEquiv I n).surjective
  obtain ⟨x, hx⟩ := limMap_surjective_of_isArtinian φ hφ y
  refine ⟨limReductionEquiv I R x, fun n ↦ ?_⟩
  have hn := congrArg (T.limπ n) hx
  rw [← LinearMap.comp_apply, limπ_comp_limMap, LinearMap.comp_apply] at hn
  have hφn : (φ.app (op n)).hom = fₗ n := rfl
  have hyn : T.limπ n y = b n := by rw [limπ_apply]
  have hvalue : fₗ n ((reduction I R).limπ n x) = b n :=
    (LinearMap.congr_fun hφn _).symm.trans (hn.trans hyn)
  exact (congrArg (f n) (reductionTermEquiv_limπ I x n).symm).trans
    ((hfₗ n _).symm.trans hvalue)

end AdicCompletion
