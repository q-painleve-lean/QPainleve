/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Artinian.Defs
import QPainleve.Algebra.Category.ModuleCat.Tower
import TauCeti.Algebra.Category.ModuleCat.Tower.Reduction

/-!
# Compatible lifts from an adic completion

If the power quotients of an ideal are Artinian modules, a compatible system
of surjections out of them lifts compatible families to the adic completion.
This includes maximal-ideal powers in a Noetherian local ring.
-/

public section

open CategoryTheory Opposite TauCeti

namespace AdicCompletion

universe u

variable {R : Type u} [CommRing R]

private noncomputable def reductionQuotientEquiv (I : Ideal R) (n : ℕ) :
    (ModuleTower.reduction I R).obj (op n) ≃ₗ[R] R ⧸ I ^ (n + 1) :=
  (ModuleTower.quotientsObjEquiv (fun j ↦ I ^ (j + 1) • ⊤)
    (I.pow_succ_smul_top_antitone R) n).trans (Submodule.quotEquivOfEq _ _ (Ideal.mul_top _))

private theorem reductionQuotientEquiv_reductionπ (I : Ideal R) (n : ℕ) (r : R) :
    reductionQuotientEquiv I n (ModuleTower.reductionπ I R n r) = Ideal.Quotient.mk _ r := by
  simp only [reductionQuotientEquiv, LinearEquiv.trans_apply,
    ModuleTower.quotientsObjEquiv_quotientsπ, Submodule.quotEquivOfEq_mk]
  rfl

private theorem reductionProjection_of_evalₐ_eq_mk
    {I : Ideal R} {x : AdicCompletion I R} {n : ℕ} {r : R}
    (hr : evalₐ I (n + 1) x = Ideal.Quotient.mk _ r) :
    (ModuleTower.reduction I R).limπ n ((ModuleTower.limReductionEquiv I R).symm x) =
      ModuleTower.reductionπ I R n r := by
  have hle := (Ideal.mul_top (I ^ (n + 1))).ge
  have he : x.val (n + 1) = Submodule.Quotient.mk r := by
    rw [← eval_apply, ← factor_evalₐ_eq_eval I x hle, hr, Ideal.Quotient.factor_mk]
    rfl
  exact ModuleTower.limπ_limReductionEquiv_symm_apply I R he

/-- A compatible family in an inverse system of quotient rings of the successive
power quotients lifts to an element of the adic completion when the power
quotients are Artinian as modules over the base ring. -/
theorem exists_evalₐ_eq_of_compatible_quotients
    (I : Ideal R) [∀ n : ℕ, IsArtinian R (R ⧸ I ^ (n + 1))]
    {B : ℕ → Type u} [∀ n, CommRing (B n)] (q : ∀ n, (R ⧸ I ^ (n + 1)) →+* B n)
    (t : ∀ n, B (n + 1) →+* B n) (hq : ∀ n, Function.Surjective (q n))
    (h : ∀ n, (t n).comp (q (n + 1)) =
      (q n).comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))
    (y : ∀ n, B n) (hy : ∀ n, t n (y (n + 1)) = y n) :
    ∃ x : AdicCompletion I R, ∀ n, q n (evalₐ I (n + 1) x) = y n := by
  let a (n : ℕ) : R →+* B n := (q n).comp (Ideal.Quotient.mk _)
  let (n : ℕ) : Algebra R (B n) := (a n).toAlgebra
  have ht (n : ℕ) (r : R) : t n (a (n + 1) r) = a n r :=
    DFunLike.congr_fun (h n) (Ideal.Quotient.mk _ r)
  let T (n : ℕ) : B (n + 1) →ₐ[R] B n := { t n with commutes' := ht n }
  let G : ModuleTower.{u} R :=
    Functor.ofOpSequence (X := fun n ↦ ModuleCat.of R (B n))
      (fun n ↦ ModuleCat.ofHom (T n).toLinearMap)
  have hT (n : ℕ) : G.map (homOfLE (Nat.le_succ n)).op =
      ModuleCat.ofHom (T n).toLinearMap :=
    Functor.ofOpSequence_map_homOfLE_succ _ n
  let F := ModuleTower.reduction I R
  let Q (n : ℕ) : R ⧸ I ^ (n + 1) →ₐ[R] B n := { q n with commutes' := fun _ ↦ rfl }
  let l (n : ℕ) : F.obj (op n) →ₗ[R] B n :=
    (Q n).toLinearMap ∘ₗ (reductionQuotientEquiv I n).toLinearMap
  have hl (n : ℕ) (r : R) : l n (ModuleTower.reductionπ I R n r) = a n r :=
    congrArg (q n) (reductionQuotientEquiv_reductionπ I n r)
  let f : F ⟶ G := NatTrans.ofOpSequence (fun n ↦ ModuleCat.ofHom (l n)) fun n ↦ by
    rw [hT n]
    apply ModuleCat.hom_ext
    apply ModuleTower.quotients_hom_ext
    refine LinearMap.ext fun r ↦ ?_
    -- Evaluate the categorical composites on representatives of the source quotient.
    change l n ((F.map (homOfLE (Nat.le_succ n)).op).hom
      (ModuleTower.reductionπ I R (n + 1) r)) =
      t n (l (n + 1) (ModuleTower.reductionπ I R (n + 1) r))
    rw [← ModuleTower.transition_def, ModuleTower.transition_quotientsπ, hl, hl, ht]
  have hsurj (n : ℕ) : Function.Surjective (f.app (op n)).hom := by
    intro z
    obtain ⟨r, hr⟩ := (hq n).comp Ideal.Quotient.mk_surjective z
    exact ⟨ModuleTower.reductionπ I R n r, (hl n r).trans hr⟩
  let (n : ℕ) : IsArtinian R (F.obj (op n)) :=
    isArtinian_of_injective (reductionQuotientEquiv I n).toLinearMap
      (reductionQuotientEquiv I n).injective
  let z : G.lim := ⟨y, G.mem_lim.mpr fun n ↦ by
    rw [ModuleTower.transition_def, hT n]
    exact hy n⟩
  obtain ⟨w, hw⟩ := ModuleTower.limMap_surjective_of_isArtinian f hsurj z
  let x := ModuleTower.limReductionEquiv I R w
  refine ⟨x, fun n ↦ ?_⟩
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I (n + 1) x)
  have hp : F.limπ n w = ModuleTower.reductionπ I R n r := by
    simpa only [x, LinearEquiv.symm_apply_apply] using reductionProjection_of_evalₐ_eq_mk hr.symm
  have hn : G.limπ n (ModuleTower.limMap f w) = (f.app (op n)).hom (F.limπ n w) := by
    simpa only [LinearMap.comp_apply] using
      LinearMap.congr_fun (ModuleTower.limπ_comp_limMap f n) w
  rw [hw, ModuleTower.limπ_apply] at hn
  have hval : l n (F.limπ n w) = y n := hn.symm
  exact (congrArg (q n) hr.symm).trans ((hl n r).symm.trans (hp.symm ▸ hval))

end AdicCompletion
