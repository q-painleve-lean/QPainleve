/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.Pullback
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Coefficient change for signed cluster relations

Equality of independent X pullbacks in characteristic zero implies equality over
every field. For a given target field, the Laurent polynomials over the integers
whose reductions are nonzero form the denominators of a common localization.
Every coordinate reached by a word lifts to this localization. At a mutation,
both the pivot and its mutation binomial reduce to nonzero rational functions
because the preceding word acts by a field automorphism.
-/

open QPainleve.Cluster Quiver TauCeti

namespace Quiver.Path

variable {ι : Type*}
variable (k K : Type*) [Field k] [Field K]

local notation "L" => LaurentRing ℤ ι
local notation "F[" k "]" => FractionRing (LaurentRing k ι)

private noncomputable def changeLaurentCoefficients : L →+* LaurentRing k ι :=
  AddMonoidAlgebra.mapRingHom (ι →₀ ℤ) (Int.castRingHom k)

private noncomputable def reduceLaurent : L →+* F[k] :=
  (algebraMap (LaurentRing k ι) F[k]).comp (changeLaurentCoefficients k)

local notation "P[" k "]" => RingHom.ker (reduceLaurent (ι := ι) k)
local notation "R[" k "]" => Localization.AtPrime P[k]

private theorem reduceLaurent_xCoordinate (i : ι) :
    reduceLaurent k (LaurentRing.X i : L) = xCoordinate k i := by
  simp [reduceLaurent, changeLaurentCoefficients, LaurentRing.X_def, xCoordinate_def]

private theorem changeLaurentCoefficients_injective [CharZero K] :
    Function.Injective (changeLaurentCoefficients (ι := ι) K) :=
  AddMonoidAlgebra.map_injective (Int.castRingHom K).toAddMonoidHom Int.cast_injective

local instance : (P[k] : Ideal L).IsPrime := RingHom.ker_isPrime _

private noncomputable def specialize : R[k] →+* F[k] :=
  IsLocalization.lift (M := P[k].primeCompl) (g := reduceLaurent k)
    fun s ↦ isUnit_iff_ne_zero.mpr (Ideal.mem_primeCompl_iff.mp s.property)

private theorem primeCompl_le_comap [CharZero K] :
    P[k].primeCompl ≤ (nonZeroDivisors (LaurentRing K ι)).comap (changeLaurentCoefficients K) :=
  (Ideal.primeCompl_le_nonZeroDivisors P[k]).trans
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (changeLaurentCoefficients_injective K))

private noncomputable def generic [CharZero K] : R[k] →+* F[K] :=
  IsLocalization.map (M := P[k].primeCompl) (T := nonZeroDivisors (LaurentRing K ι))
    F[K] (changeLaurentCoefficients K) (primeCompl_le_comap k K)

private theorem generic_injective [CharZero K] :
    Function.Injective (generic (ι := ι) k K) :=
  IsLocalization.map_injective_of_injective' P[k].primeCompl (LaurentRing K ι) F[K]
    (Rₘ := R[k]) (f := changeLaurentCoefficients (ι := ι) K)
    (N := nonZeroDivisors (LaurentRing K ι)) (primeCompl_le_comap k K)
    (by simp) (changeLaurentCoefficients_injective K)

private theorem isUnit_of_specialize_ne_zero {x : R[k]} (h : specialize k x ≠ 0) : IsUnit x := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq P[k].primeCompl x
  apply (IsLocalization.AtPrime.isUnit_mk'_iff R[k] P[k] a s).mpr
  apply Ideal.mem_primeCompl_iff.mpr
  intro ha
  apply h
  exact (IsLocalization.lift_mk'_spec _ a 0 s).mpr (by simpa using ha)

variable [DecidableEq ι] [CharZero K] {B C D : SkewExchangeMatrix ι}

private theorem exists_lift_xPullback_xCoordinate (w : Word B C) :
    ∀ i : ι, ∃ x : R[k],
      generic k K x = w.xPullback K (xCoordinate K i) ∧
      specialize k x = w.xPullback k (xCoordinate k i) := by
  induction w with
  | nil =>
    intro i
    refine ⟨algebraMap L R[k] (LaurentRing.X i), ?_, ?_⟩
    · simp only [generic, IsLocalization.map_eq, xPullback_nil, AlgEquiv.one_apply]
      exact reduceLaurent_xCoordinate K i
    · simp [specialize, reduceLaurent_xCoordinate]
  | @cons C D w s ih =>
    intro i
    let x (j : ι) := (ih j).choose
    have hK (j : ι) : generic k K (x j) = w.xPullback K (xCoordinate K j) :=
      (ih j).choose_spec.1
    have hk (j : ι) : specialize k (x j) = w.xPullback k (xCoordinate k j) :=
      (ih j).choose_spec.2
    have hunit (j : ι) : IsUnit (x j) :=
      isUnit_of_specialize_ne_zero k (by
        rw [hk]
        exact (map_ne_zero (w.xPullback k)).mpr (xCoordinate_ne_zero k j))
    have hbinomial (j : ι) : IsUnit (1 + x j) :=
      isUnit_of_specialize_ne_zero k (by
        rw [map_add, map_one, hk, ← map_one (w.xPullback k), ← map_add]
        exact (map_ne_zero (w.xPullback k)).mpr (one_add_xCoordinate_ne_zero k j))
    let u (j : ι) : R[k]ˣ := (hunit j).unit
    let b (j : ι) : R[k]ˣ := (hbinomial j).unit
    have hu (j : ι) : (u j : R[k]) = x j := (hunit j).unit_spec
    have hb (j : ι) : (b j : R[k]) = 1 + x j := (hbinomial j).unit_spec
    obtain ⟨g, rfl⟩ := s
    simp only [xPullback_cons, Step.xPullback_eq, AlgEquiv.mul_apply]
    cases g with
    | permute σ => simpa using ih (σ i)
    | invert =>
      refine ⟨↑(u i ^ (-1 : ℤ)), ?_, ?_⟩
      · simp [hu, hK]
      · simp [hu, hk]
    | mutate p =>
      rcases eq_or_ne i p with rfl | hip
      · refine ⟨↑(u i ^ (-1 : ℤ)), ?_, ?_⟩
        · simp [hu, hK]
        · simp [hu, hk]
      · refine ⟨x i * ↑(u p ^ max (C.matrix i p) 0) * ↑(b p ^ (-C.matrix i p)), ?_, ?_⟩
        · have hpow (g : R[k]ˣ) (n : ℤ) :
              generic k K (↑(g ^ n) : R[k]) = generic k K (g : R[k]) ^ n :=
            map_zpow ((generic (ι := ι) k K).toMonoidHom.comp (Units.coeHom R[k])) g n
          simp [xMutation_apply_of_ne _ _ _ hip, hpow, hu, hb, hK]
        · have hpow (g : R[k]ˣ) (n : ℤ) :
              specialize k (↑(g ^ n) : R[k]) = specialize k (g : R[k]) ^ n :=
            map_zpow ((specialize (ι := ι) k).toMonoidHom.comp (Units.coeHom R[k])) g n
          simp [xMutation_apply_of_ne _ _ _ hip, hpow, hu, hb, hk]

/-- An equality of signed word pullbacks in characteristic zero holds over every
field. The words have a common source and may have different terminal seeds. -/
public theorem xPullback_eq_of_charZero {w : Word B C} {v : Word B D}
    (h : w.xPullback K = v.xPullback K) : w.xPullback k = v.xPullback k := by
  apply algEquiv_ext_xCoordinate
  intro i
  obtain ⟨x, hxK, hxk⟩ := exists_lift_xPullback_xCoordinate k K w i
  obtain ⟨y, hyK, hyk⟩ := exists_lift_xPullback_xCoordinate k K v i
  have hxy : x = y := generic_injective k K (by rw [hxK, hyK, h])
  rw [← hxk, ← hyk, hxy]

end Quiver.Path
