/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Tropical.Basic
public import TauCeti.Algebra.Cluster.YSeed.Geometric

/-!
# Tropical transport of frozen rows

Finitely supported integer exponents give the coefficients of a `TauCeti.Trop` seed.
Evaluating a signed word on these exponents transports the frozen rows simultaneously.
Each row of the result is the ordinary integer evaluation of the same word on that row.
The comparison with extended exchange matrices uses `TauCeti.YSeed.toExtendedMatrix_mutation`
and `TauCeti.YSeed.toExtendedMatrix_reindex`.
-/

public section

namespace QPainleve.Cluster

open CategoryTheory Quiver
open TauCeti (ExchangeMatrix YSeed)

variable {ι J : Type*} [DecidableEq ι]
variable {B C : SkewExchangeMatrix ι}

namespace Generator

/-- Each row of the tropical exponent matrix is transformed independently. -/
@[simp]
theorem tropical_finsupp_apply (g : Generator ι) (B : SkewExchangeMatrix ι)
    (b : ι → J →₀ ℤ) (j : J) (i : ι) :
    g.tropical B b i j = g.tropical B (fun k ↦ b k j) i := by
  cases g with
  | mutate k =>
    by_cases h : i = k
    · subst i
      simp
    · simp only [tropical_mutate_of_ne_smul B _ h, Finsupp.sub_apply, Finsupp.add_apply,
        Finsupp.smul_apply, Finsupp.inf_apply, Finsupp.zero_apply]
  | permute σ => simp
  | invert => simp

/-- In the extended matrix, simultaneous tropical mutation is native exchange matrix mutation. -/
theorem toExtendedMatrix_tropical_mutate [DecidableEq J] (B : SkewExchangeMatrix ι)
    (b : ι → J →₀ ℤ) (k : ι) :
    ((B.mutate k).tropicalSeed ((mutate k).tropical B b)).toExtendedMatrix =
      (B.tropicalSeed b).toExtendedMatrix.mutation k := by
  rw [tropicalSeed_mutation, YSeed.toExtendedMatrix_mutation]

/-- Relabeling the mutable indices of a tropical seed leaves the frozen labels fixed. -/
@[simp]
theorem toExtendedMatrix_tropical_permute (B : SkewExchangeMatrix ι)
    (b : ι → J →₀ ℤ) (σ : Equiv.Perm ι) :
    ((B.reindex σ.symm).tropicalSeed ((permute σ).tropical B b)).toExtendedMatrix =
      ExchangeMatrix.reindex (row' := Function.Embedding.inl)
        (Equiv.sumCongr σ.symm (Equiv.refl J)) σ.symm (fun _ ↦ by simp)
        (B.tropicalSeed b).toExtendedMatrix := by
  have hexponents : (permute σ).tropical B b = b ∘ σ :=
    funext (tropical_permute_apply B b σ)
  have hseed := SkewExchangeMatrix.tropicalSeed_reindex B b σ.symm
  rw [Equiv.symm_symm] at hseed
  rw [hexponents, hseed, YSeed.toExtendedMatrix_reindex]

/-- Simultaneous inversion negates both the principal and the frozen entries. -/
@[simp]
theorem toExtendedMatrix_tropical_invert_matrix (B : SkewExchangeMatrix ι)
    (b : ι → J →₀ ℤ) :
    ((-B).tropicalSeed (invert.tropical B b)).toExtendedMatrix.matrix =
      -(B.tropicalSeed b).toExtendedMatrix.matrix := by
  ext i k
  cases i with
  | inl i => simp [SkewExchangeMatrix.val_matrix]
  | inr j => simp

end Generator

/-- Reading a frozen row after transport along a signed word agrees with transporting that row
as an integer vector. -/
@[simp]
theorem tropical_map_finsupp_apply (w : Word B C) (b : ι → J →₀ ℤ) (j : J) (i : ι) :
    DFunLike.coe (F := Equiv.Perm (ι → J →₀ ℤ))
        ((Paths.lift (tropicalPrefunctor (A := J →₀ ℤ) ι)).map w) b i j =
      DFunLike.coe (F := Equiv.Perm (ι → ℤ))
        ((Paths.lift (tropicalPrefunctor (A := ℤ) ι)).map w) (fun k ↦ b k j) i := by
  induction w generalizing i with
  | nil => rfl
  | cons w s ih =>
    simp only [tropical_map_cons_apply, Step.tropical_apply, Generator.tropical_finsupp_apply]
    rw [funext ih]

end QPainleve.Cluster
