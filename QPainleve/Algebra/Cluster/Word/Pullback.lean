/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Basic
public import QPainleve.Algebra.Cluster.XMutation.Symmetry

import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# Pullbacks of signed cluster words

Each step acts on the field of independent cluster X coordinates. The action of a path is
the composite pullback, from the function field at its target to the one at its source.
Concatenation reverses the order of application to functions, and reversing a path takes the
inverse pullback.

The generator formulas are those in `XMutation.Basic` and `XMutation.Symmetry`. Their
extension to paths uses Mathlib's `CategoryTheory.Paths.lift`.
-/

public noncomputable section

namespace QPainleve.Cluster

open Quiver

variable (k : Type*) [Field k] {ι κ : Type*}

local notation:max "Functions" ι:arg => FractionRing (AddMonoidAlgebra k (ι →₀ ℤ))

namespace Generator

/-- Pull back independent X coordinates along a mutation, relabeling, or global inversion. -/
def xPullback (B : SkewExchangeMatrix ι) : Generator ι → (Functions ι ≃ₐ[k] Functions ι)
  | .mutate p => xMutation k p (fun i ↦ B.matrix i p)
  | .permute σ => xReindex k σ
  | .invert => xInversion k ι

@[simp]
theorem xPullback_mutate (B : SkewExchangeMatrix ι) (p : ι) :
    (mutate p).xPullback k B = xMutation k p (fun i ↦ B.matrix i p) :=
  (rfl)

@[simp]
theorem xPullback_permute (B : SkewExchangeMatrix ι) (σ : Equiv.Perm ι) :
    (permute σ).xPullback k B = xReindex k σ :=
  (rfl)

@[simp]
theorem xPullback_invert (B : SkewExchangeMatrix ι) :
    invert.xPullback k B = xInversion k ι :=
  (rfl)

/-- Changing the labels of a generator intertwines its pullback with the coordinate relabeling. -/
theorem xPullback_reindex (B : SkewExchangeMatrix ι) (g : Generator ι) (e : ι ≃ κ) :
    ((g.reindex e).xPullback k (B.reindex e)).trans (xReindex k e.symm) =
      (xReindex k e.symm).trans (g.xPullback k B) := by
  cases g with
  | mutate p =>
    simpa [Function.comp_def] using xMutation_trans_xReindex k e.symm (e p) (fun i ↦ B.matrix i p)
  | permute σ => simp [Equiv.trans_assoc]
  | invert => simpa using xInversion_trans_xReindex k e.symm

end Generator

variable [DecidableEq ι] [DecidableEq κ]

namespace Step

/-- The pullback of a typed edge, computed from its generator and source exchange matrix. -/
def xPullback {B C : SkewExchangeMatrix ι} (s : Step B C) : Functions ι ≃ₐ[k] Functions ι :=
  s.generator.xPullback k B

theorem xPullback_eq {B C : SkewExchangeMatrix ι} (s : Step B C) :
    s.xPullback k = s.generator.xPullback k B :=
  (rfl)

@[simp]
theorem xPullback_toStep (B : SkewExchangeMatrix ι) (g : Generator ι) :
    Step.xPullback k (g.toStep B) = g.xPullback k B := by
  simp [xPullback_eq]

/-- The return edge induces the inverse pullback. -/
@[simp]
theorem xPullback_reverse {B C : SkewExchangeMatrix ι} (s : B ⟶ C) :
    (Step.xPullback k (Quiver.reverse s)) = (Step.xPullback k s)⁻¹ := by
  rcases s with ⟨g, rfl⟩
  cases g with
  | mutate p =>
    simp only [xPullback_eq, reverse_generator, Generator.reverse_mutate, Generator.target_mutate,
      Generator.xPullback_mutate, SkewExchangeMatrix.mutate_matrix]
    exact (xMutation_symm_matrixMutation k p B.matrix).symm
  | permute σ => simp [xPullback_eq, AlgEquiv.aut_inv]
  | invert => simp [xPullback_eq, AlgEquiv.aut_inv]

end Step

end QPainleve.Cluster

open CategoryTheory Quiver MulOpposite QPainleve.Cluster

variable (k : Type*) [Field k] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

local notation:max "Functions" ι:arg => FractionRing (AddMonoidAlgebra k (ι →₀ ℤ))
local notation:max "Aut" ι:arg => (Functions ι ≃ₐ[k] Functions ι)

namespace Quiver.Path

variable {B C D : SkewExchangeMatrix ι}

-- In the opposite group, multiplication in the one-object category gives pullback order.
private def xPullbackPrefunctor : SkewExchangeMatrix ι ⥤q SingleObj (Aut ι)ᵐᵒᵖ where
  obj _ := SingleObj.star _
  map s := op (Step.xPullback k s)

/-- Pull back functions along a word, applying its last step's pullback first. -/
def xPullback (w : Word B C) : Aut ι :=
  unop ((Paths.lift (xPullbackPrefunctor k)).map w)

@[simp]
theorem xPullback_nil : (Path.nil : Word B B).xPullback k = 1 :=
  (rfl)

@[simp]
theorem xPullback_toPath (s : B ⟶ C) : s.toPath.xPullback k = Step.xPullback k s := by
  unfold xPullback
  rw [Paths.lift_toPath]
  rfl

/-- Pullback reverses the order of concatenation on points. -/
@[simp]
theorem xPullback_comp (w : Word B C) (v : Word C D) :
    (w.comp v).xPullback k = w.xPullback k * v.xPullback k :=
  congrArg unop ((Paths.lift (xPullbackPrefunctor k)).map_comp w v)

@[simp]
theorem xPullback_cons (w : Word B C) (s : C ⟶ D) :
    (w.cons s).xPullback k = w.xPullback k * Step.xPullback k s := by
  rw [← Path.comp_toPath_eq_cons, xPullback_comp, xPullback_toPath]

/-- The reverse word pulls back by the inverse automorphism. -/
@[simp]
theorem xPullback_reverse (w : Word B C) : w.reverse.xPullback k = (w.xPullback k)⁻¹ := by
  induction w with
  | nil => simp [Path.reverse]
  | cons _ _ ih => simp [Path.reverse, ih]

/-- The word's pullback commutes with relabeling all of its exchange matrices and steps. -/
theorem xPullback_reindex (e : ι ≃ κ) (w : Word B C) :
    (((SkewExchangeMatrix.reindexPrefunctor e).mapPath w).xPullback k).trans (xReindex k e.symm) =
      (xReindex k e.symm).trans (w.xPullback k) := by
  induction w with
  | nil =>
    ext x
    simp
  | cons w s ih =>
    rename_i B' C'
    have hs := Generator.xPullback_reindex k B' s.generator e
    ext x
    have h := DFunLike.congr_fun ih ((s.generator.reindex e).xPullback k (B'.reindex e) x)
    simpa only [Prefunctor.mapPath_cons, xPullback_cons, Step.xPullback_eq,
      SkewExchangeMatrix.reindexPrefunctor_map_generator, SkewExchangeMatrix.reindexPrefunctor_obj,
      AlgEquiv.trans_apply, AlgEquiv.mul_apply] using
      h.trans (congrArg (w.xPullback k) (DFunLike.congr_fun hs x))

end Quiver.Path
