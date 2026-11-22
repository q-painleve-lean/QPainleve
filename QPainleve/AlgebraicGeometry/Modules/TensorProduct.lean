/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Tensor products of sections of scheme modules

The pure tensor of two sections gives a section of the sheaf tensor product over the same open.
Iterating this construction gives a linear map from the original module of sections to the
sections of the iterated tensor product.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Opposite
open TauCeti

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M L : X.Modules} {U V : X.Opens}

private abbrev tensorSectionMap (M L : X.Modules) :
    (M.val ⊗ L.val : PresheafOfModulesOfCommRing X.presheaf) ⟶ (M ⊗ L).val :=
  μ (SheafOfModules.forget X.ringCatSheaf) M L

/-- The section of the sheaf tensor product represented by the indicated pure tensor. -/
def tensorSection (x : Γ(M, U)) (s : Γ(L, U)) : Γ(M ⊗ L, U) :=
  (tensorSectionMap M L).app (op U) (TensorProduct.tmul Γ(X, U) x s)

/-- Scalar multiplication of the second factor acts on the tensor section. -/
@[simp]
lemma tensorSection_smul_right (x : Γ(M, U)) (r : Γ(X, U)) (s : Γ(L, U)) :
    tensorSection x (r • s) = r • tensorSection x s := by
  exact congrArg (((tensorSectionMap M L).app (op U)).hom) (TensorProduct.tmul_smul r x s)
    |>.trans (((tensorSectionMap M L).app (op U)).hom.map_smul r _)

/-- Restriction commutes with pure tensors of sections. -/
@[simp]
lemma map_tensorSection (i : V ⟶ U) (x : Γ(M, U)) (s : Γ(L, U)) :
    (M ⊗ L).presheaf.map i.op (tensorSection x s) =
      tensorSection (M.presheaf.map i.op x) (L.presheaf.map i.op s) :=
  (PresheafOfModules.naturality_apply (tensorSectionMap M L) i.op
    (TensorProduct.tmul Γ(X, U) x s)).symm

/-- The result of tensoring a sheaf on the right by `L` repeatedly. -/
abbrev tensorTwist (M L : X.Modules) (n : ℕ) : X.Modules :=
  n.rec M (fun _ A ↦ A ⊗ L)

/-- Twisting zero times returns the original sheaf. -/
@[simp]
lemma tensorTwist_zero (M L : X.Modules) : M.tensorTwist L 0 = M := (rfl)

/-- Each additional twist tensors once more by the same sheaf. -/
lemma tensorTwist_succ (M L : X.Modules) (n : ℕ) :
    M.tensorTwist L (n + 1) = M.tensorTwist L n ⊗ L := (rfl)

/-- Tensor a section with `n` copies of a section of `L`. -/
def tensorSectionPow (s : Γ(L, U)) : (n : ℕ) → Γ(M, U) →ₗ[Γ(X, U)] Γ(M.tensorTwist L n, U)
  | 0 => LinearMap.id
  | n + 1 =>
    (((tensorSectionMap (M.tensorTwist L n) L).app (op U)).hom.comp
      ((TensorProduct.mk Γ(X, U) _ _).flip s)).comp (tensorSectionPow s n)

/-- Tensoring a section by the zeroth power leaves it unchanged. -/
lemma tensorSectionPow_zero (s : Γ(L, U)) (x : Γ(M, U)) :
    tensorSectionPow s 0 x = x := (rfl)

/-- Tensoring by a successor power applies one more pure tensor. -/
lemma tensorSectionPow_succ (s : Γ(L, U)) (n : ℕ) (x : Γ(M, U)) :
    tensorSectionPow s (n + 1) x = tensorSection (tensorSectionPow s n x) s := (rfl)

/-- Restriction commutes with multiplication by a power of a section. -/
@[simp]
lemma map_tensorSectionPow (i : V ⟶ U) (s : Γ(L, U)) (n : ℕ) (x : Γ(M, U)) :
    (M.tensorTwist L n).presheaf.map i.op (tensorSectionPow s n x) =
      tensorSectionPow (L.presheaf.map i.op s) n (M.presheaf.map i.op x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (map_tensorSection i (tensorSectionPow s n x) s).trans
      (congrArg (fun a ↦ tensorSection a (L.presheaf.map i.op s)) ih)

/-- Scalar multiplication of the first factor acts on the tensor section. -/
@[simp]
lemma tensorSection_smul_left (x : Γ(M, U)) (r : Γ(X, U)) (s : Γ(L, U)) :
    tensorSection (r • x) s = r • tensorSection x s := by
  let f := ((tensorSectionMap M L).app (op U)).hom
  exact (congrArg f (TensorProduct.smul_tmul' (R := Γ(X, U)) r x s).symm).trans
    (f.map_smul r _)

/-- Rescaling the twisting section rescales the result by the corresponding power. -/
lemma tensorSectionPow_smul_section (s : Γ(L, U)) (r : Γ(X, U)) (n : ℕ) (x : Γ(M, U)) :
    tensorSectionPow (r • s) n x = tensorSectionPow s n (r ^ n • x) := by
  induction n with
  | zero => simp only [tensorSectionPow_zero, pow_zero, one_smul]
  | succ n ih =>
    calc
      tensorSectionPow (r • s) (n + 1) x =
          r • tensorSection (tensorSectionPow s n (r ^ n • x)) s := by
        rw [tensorSectionPow_succ, tensorSection_smul_right, ih]
      _ = tensorSection (tensorSectionPow s n (r ^ (n + 1) • x)) s := by
        simp only [pow_succ', mul_smul, (tensorSectionPow s n).map_smul, tensorSection_smul_left]
      _ = tensorSectionPow s (n + 1) (r ^ (n + 1) • x) := (tensorSectionPow_succ _ _ _).symm

/-- Tensoring by a fixed section is natural in the first sheaf. -/
lemma tensorSection_naturality_left {N : X.Modules} (f : M ⟶ N) (x : Γ(M, U))
    (s : Γ(L, U)) : (f ▷ L).app U (tensorSection x s) = tensorSection (f.app U x) s :=
  (congrArg (fun p ↦ p.app (op U) (TensorProduct.tmul Γ(X, U)
    (M := Γ(M, U)) (N := Γ(L, U)) x s))
    (μ_natural_left (SheafOfModules.forget X.ringCatSheaf) f L)).symm

/-- Consecutive twists add their exponents. -/
lemma tensorTwist_add (M L : X.Modules) (n m : ℕ) :
    M.tensorTwist L (n + m) = (M.tensorTwist L n).tensorTwist L m := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (fun F : X.Modules ↦ F ⊗ L) ih

/-- Tensoring by two successive powers agrees with tensoring by the sum of their exponents. -/
lemma tensorSectionPow_add (s : Γ(L, U)) (n m : ℕ) (x : Γ(M, U)) :
    (eqToHom (tensorTwist_add M L n m)).app U (tensorSectionPow s (n + m) x) =
      tensorSectionPow s m (tensorSectionPow s n x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h : eqToHom (tensorTwist_add M L n (m + 1)) =
        eqToHom (tensorTwist_add M L n m) ▷ L :=
      (eqToHom_map (tensorRight L) (tensorTwist_add M L n m)).symm
    have hstep := tensorSection_naturality_left (eqToHom (tensorTwist_add M L n m))
      (tensorSectionPow s (n + m) x) s
    simp only [Nat.add_succ, h]
    exact hstep.trans (congrArg (tensorSection · s) ih)

/-- Iterated tensor products of quasi-coherent modules are quasi-coherent. -/
lemma isQuasicoherent_tensorTwist [M.IsQuasicoherent] [L.IsQuasicoherent] (n : ℕ) :
    (M.tensorTwist L n).IsQuasicoherent := by
  induction n with
  | zero => exact ‹M.IsQuasicoherent›
  | succ n ih => exact inferInstanceAs (M.tensorTwist L n ⊗ L).IsQuasicoherent

end AlgebraicGeometry.Scheme.Modules
