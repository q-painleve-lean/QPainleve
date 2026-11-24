/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.RationalMap
public import QPainleve.SignedClusterModularGroup.Realization.Basic

import QPainleve.Algebra.Cluster.Word.Inversion

/-!
# Realizing signed cluster loops

Orientation-preserving realizations of inversion-free loops and one
orientation-reversing realization of an odd loop suffice to realize every
signed loop, with the branch sign given by the number of inversions.
-/

public section

open AlgebraicGeometry CategoryTheory Quiver
open QPainleve.CharacterTorus QPainleve.Cluster TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace QPainleve.SignedClusterModularGroup.GeometricRealization

universe u

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k]
  {ι : Type u} [Finite ι] [DecidableEq ι] {E : SkewExchangeMatrix ι}
  {n : ℕ} [NeZero n] {L : Type u} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  {T : Over (Spec (CommRingCat.of k))} [Nonempty T.left] [Smooth T.hom]
  {P : Point T → MarkedSurface k n B (scheme k (ι →₀ ℤ))}

private theorem exists_realization_of_even_inversionCount
    (hfree : ∀ w : Word E E, w.inversionCount = 0 → ∃ (C : T.left.PartialMap T.left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T.hom T.hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C (w.xRationalMap k), R.orientation = 1)
    (w : Word E E) (hw : Even w.inversionCount) :
    ∃ (C : T.left.PartialMap T.left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T.hom T.hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C (w.xRationalMap k), R.orientation = 1 := by
  obtain ⟨v, hv, he⟩ := w.exists_xPullback_eq_of_even_inversionCount k hw
  have h : w.xRationalMap k = v.xRationalMap k := (Path.xRationalMap_eq_iff k w v).mpr he
  obtain ⟨C, hC, hCO, R, hR⟩ := hfree v hv
  let := hC
  let := hCO
  exact ⟨C, hC, hCO, R.congrMaps rfl h.symm, by simp [hR]⟩

/-- For a fixed marked family, every signed loop admits a geometric realization
with the orientation given by its inversion parity, provided inversion-free loops
have positive realizations and one odd loop has a negative realization. -/
theorem exists_of_inversionFree_and_odd [PreirreducibleSpace T.left]
    (hfree : ∀ w : Word E E, w.inversionCount = 0 → ∃ (C : T.left.PartialMap T.left)
      (hC : IsDominant C.hom) (hCO : C.IsOver T.hom T.hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C (w.xRationalMap k), R.orientation = 1)
    (o : Word E E) (ho : Odd o.inversionCount)
    {D : T.left.PartialMap T.left} [IsDominant D.hom] [D.IsOver T.hom T.hom]
    (O : GeometricRealization P P D (o.xRationalMap k)) (hO : O.orientation = -1) (w : Word E E) :
    ∃ (C : T.left.PartialMap T.left) (hC : IsDominant C.hom) (hCO : C.IsOver T.hom T.hom),
      letI := hC
      letI := hCO
      ∃ R : GeometricRealization P P C (w.xRationalMap k),
        R.orientation = (-1 : ℤˣ) ^ w.inversionCount := by
  rcases Nat.even_or_odd w.inversionCount with he | hw
  · rw [he.neg_one_pow]
    exact exists_realization_of_even_inversionCount hfree w he
  · -- Append the inverse of the fixed odd loop to obtain an even word.
    let v := w.comp o.reverse
    have hv : Even v.inversionCount := by
      simpa only [v, Path.inversionCount_comp, Path.inversionCount_reverse] using hw.add_odd ho
    obtain ⟨C, hC, hCO, R, hR⟩ := exists_realization_of_even_inversionCount hfree v hv
    let := hC
    let := hCO
    have hmap : (v.xRationalMap k).comp (o.xRationalMap k) = w.xRationalMap k := by
      rw [← Path.xRationalMap_comp, Path.xRationalMap_eq_iff]
      simp only [v, Path.xPullback_comp, Path.xPullback_reverse, inv_mul_cancel_right]
    refine ⟨C.comp D, inferInstance, inferInstance, ?_⟩
    have hsign : (R.comp O).orientation = (-1 : ℤˣ) ^ w.inversionCount := by
      rw [comp_orientation, hR, hO, mul_one, hw.neg_one_pow]
    exact ⟨(R.comp O).congrMaps rfl hmap, by simp [hsign]⟩

end QPainleve.SignedClusterModularGroup.GeometricRealization
