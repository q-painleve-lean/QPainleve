/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Canonical
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Picard
public import TauCeti.AlgebraicGeometry.Chow.SurfaceIntersection.Basic
public import TauCeti.AlgebraicGeometry.Noetherian
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.EulerCharacteristic
import QPainleve.AlgebraicGeometry.Blowup.Tower.Canonical
import QPainleve.AlgebraicGeometry.Chow.Isomorphism
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.Cohomology.Support
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction

/-!
# The Picard pairing of a tower of point blowups

The Picard marking of a tower of point blowups identifies the intersection pairing with
the base pairing and one orthogonal summand of square `-1` per blowup. In the same marking
the canonical class has every exceptional coefficient equal to one. For two markings
of the same resolved class, this compares the canonical intersections on their bases.

The calculation iterates the exceptional twist formula for Euler characteristics. Finiteness
and vanishing for line-bundle cohomology propagate along the tower from its projective base.
For the one-point Picard and canonical class formulas, see
[Hacking, *Compact Complex Surfaces*, Propositions 7.1 and 7.2][Hacking].

[Hacking]: https://paulhacking.github.io/surfaces.pdf#page=34
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open LineBundleClass
open scoped BigOperators

universe u

namespace QPainleve.BlowupTower

variable {X Y : Scheme.{u}} {n : ℕ} {T : BlowupTower X n Y}
variable (k : Type u) [Field k] [X.Over (Spec (.of k))]
variable [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "f" => (X ↘ Spec (CommRingCat.of k))

section EulerCharacteristic

variable [IsAlgClosed k] [IsIntegral X] [X.IsProjectiveOver k]

open Scheme.Modules in
private theorem cohomology_picardHom_aux (hT : IsClosedPointTower X T) :
    ∀ (g : Y ⟶ Spec (.of k)), g = T.toBase ≫ f →
      letI : Y.Over (Spec (.of k)) := ⟨g⟩
      ∀ (a : Additive (LineBundleClass X)) (b : Fin n → ℤ) (L : InvertibleSheaf Y),
        mk L = (T.picardHom (a, b)).toMul →
          (∀ q, FiniteDimensional k (Cohomology L.obj q) ∧
            (2 < q → Subsingleton (Cohomology L.obj q))) ∧
          2 * (eulerCharBelow k (mk L) 3 - eulerCharBelow k a.toMul 3) =
            ∑ j, b j * (1 - b j) := by
  have : IsNoetherian X := isNoetherian_of_finiteType f
  induction hT with
  | nil =>
    intro g hg a b L hL
    rw [toBase_nil, Category.id_comp] at hg
    subst g
    rw [picardHom_nil] at hL
    refine ⟨fun q ↦ ⟨moduleFinite_cohomology_of_isProjectiveOver k L.obj q, ?_⟩, ?_⟩
    · intro hq
      exact subsingleton_cohomology_of_projective_dim_lt (k := k) L.obj
        ((topologicalKrullDim_eq_of_smoothOfRelativeDimension f (n := 2)).le.trans_lt
          (by exact_mod_cast hq))
    · rw [Finset.sum_of_isEmpty]
      exact (congrArg (fun c ↦ 2 * (eulerCharBelow k c 3 - eulerCharBelow k a.toMul 3)) hL).trans
        (by ring)
  | @snoc d W S I hS p hp hI ih =>
    subst I
    intro g' hg' a b M hM
    rw [toBase_snoc, Category.assoc] at hg'
    subst g'
    let g := S.toBase ≫ f
    let : W.Over (Spec (.of k)) := ⟨g⟩
    let : (W.fromSpecResidueField p).ker.blowup.Over (Spec (.of k)) :=
      ⟨(W.fromSpecResidueField p).ker.blowupToBase ≫ g⟩
    have : IsNoetherian W := S.isNoetherian
    have : SmoothOfRelativeDimension 2 g := hS.smoothOfRelativeDimension f
    have : Smooth g := SmoothOfRelativeDimension.smooth 2 g
    have : IsRegular W := IsRegular.of_smooth g
    have hdim :=
      ((smoothOfRelativeDimension_iff_ringKrullDim_stalk_eq g 2).mp inferInstance).2 p hp
    have hrat : IsIso (W.fromSpecResidueField p ≫ g) := by
      rw [← SpecMap_residueFieldIsoBase_inv g p hp]
      infer_instance
    obtain ⟨L, hL⟩ := mk_surjective (S.picardHom (a, fun j ↦ b j.castSucc)).toMul
    obtain ⟨hcoh, hχ⟩ := ih g rfl a (fun j ↦ b j.castSucc) L hL
    rw [picardHom_snoc_apply_toMul, ← hL,
      Scheme.IdealSheafData.blowupExceptionalClass_def, inv_zpow, ← zpow_neg] at hM
    have hstep := Scheme.IdealSheafData.two_mul_eulerCharBelow_sub_pointBlowup_exceptional_twist
      p k hp hdim hrat L hcoh (b (Fin.last d))
    dsimp only at hstep
    rw [← hM] at hstep
    refine ⟨fun q ↦ Scheme.IdealSheafData.pointBlowup_exceptional_twist_cohomology_of_cohomology
      p k hp hdim hrat L hcoh (b (Fin.last d)) M hM q, ?_⟩
    rw [Fin.sum_univ_castSucc]
    calc
      _ = 2 * (eulerCharBelow k (mk M) 3 - eulerCharBelow k (mk L) 3) +
          2 * (eulerCharBelow k (mk L) 3 - eulerCharBelow k a.toMul 3) := by
        rw [← mul_add, sub_add_sub_cancel]
      _ = _ := (congrArg₂ (· + ·) hstep hχ).trans (add_comm _ _)

/-- Every line bundle on a tower of closed point blowups of a smooth integral projective
surface has finite-dimensional cohomology, vanishing above degree two. -/
theorem IsClosedPointTower.lineBundle_cohomology (hT : IsClosedPointTower X T)
    (L : InvertibleSheaf Y) (q : ℕ) :
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    FiniteDimensional k (Scheme.Modules.Cohomology L.obj q) ∧
      (2 < q → Subsingleton (Scheme.Modules.Cohomology L.obj q)) := by
  have : IsNoetherian X := isNoetherian_of_finiteType f
  obtain ⟨⟨a, b⟩, hab⟩ := (hT.bijective_picardHom f).surjective (Additive.ofMul (mk L))
  exact (cohomology_picardHom_aux k hT (T.toBase ≫ f) rfl a b L
    (congrArg Additive.toMul hab).symm).1 q

/-- The change in twice the Euler characteristic in the Picard coordinates of a point-blowup
tower is the sum of the exceptional corrections `b * (1 - b)`. -/
theorem two_mul_eulerCharBelow_sub_picardHom (hT : IsClosedPointTower X T)
    (a : Additive (LineBundleClass X) × (Fin n → ℤ)) :
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    2 * (eulerCharBelow k (T.picardHom a).toMul 3 - eulerCharBelow k a.1.toMul 3) =
      ∑ j, a.2 j * (1 - a.2 j) := by
  obtain ⟨a, b⟩ := a
  obtain ⟨L, hL⟩ := mk_surjective (T.picardHom (a, b)).toMul
  simpa only [hL] using (cohomology_picardHom_aux k hT (T.toBase ≫ f) rfl a b L hL).2

/-- In the Picard marking the intersection pairing is the base pairing minus the dot product
of the exceptional coefficients. The exceptional generators are full pullbacks along all
later stages, so the formula includes towers with infinitely near centers. -/
theorem classIntersectionNumber_picardMarking (hT : IsClosedPointTower X T)
    (a b : Additive (LineBundleClass X) × (Fin n → ℤ)) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    Chow.classIntersectionNumber k Y (T.picardMarking hT f a).toMul
      (T.picardMarking hT f b).toMul =
      Chow.classIntersectionNumber k X a.1.toMul b.1.toMul - ∑ j, a.2 j * b.2 j := by
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
  have : IsNoetherian X := isNoetherian_of_finiteType f
  dsimp only
  rw [picardMarking_apply, picardMarking_apply,
    Chow.classIntersectionNumber_eq, Chow.classIntersectionNumber_eq]
  have hzero := two_mul_eulerCharBelow_sub_picardHom k hT 0
  have ha := two_mul_eulerCharBelow_sub_picardHom k hT (-a)
  have hb := two_mul_eulerCharBelow_sub_picardHom k hT (-b)
  have hab := two_mul_eulerCharBelow_sub_picardHom k hT (-a + -b)
  -- Polarizing the doubled Euler correction gives twice the negative dot product.
  have hsum : (∑ j, (-a.2 j + -b.2 j) * (1 - (-a.2 j + -b.2 j))) =
      (∑ j, -a.2 j * (1 - -a.2 j)) + (∑ j, -b.2 j * (1 - -b.2 j)) -
        2 * ∑ j, a.2 j * b.2 j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [map_zero, map_neg, map_add, Prod.fst_zero, Prod.fst_add, Prod.fst_neg,
    Prod.snd_zero, Prod.snd_add, Prod.snd_neg,
    toMul_zero, toMul_neg, toMul_add, Pi.neg_apply, Pi.add_apply, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero] at hzero ha hb hab
  omega

variable {k} in
/-- Intersecting a marked class with the total exceptional class of one blowup
reads the negative of that blowup's coefficient. -/
@[simp]
theorem classIntersectionNumber_picardHom_exceptionalClass (hT : IsClosedPointTower X T)
    (a : Additive (LineBundleClass X) × (Fin n → ℤ)) (j : Fin n) :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    Chow.classIntersectionNumber k Y (T.picardHom a).toMul (T.exceptionalClass j) =
      -a.2 j := by
  let : IsNoetherian X := isNoetherian_of_finiteType f
  have h := classIntersectionNumber_picardMarking k hT a (0, Pi.single j 1)
  simpa [picardMarking_apply, picardHom_apply_single, Pi.single_apply,
    mul_ite, Finset.sum_ite_eq', Chow.classIntersectionNumber_one_right] using h

/-- The pullback of two Picard classes along a closed-point blowup tower preserves their
surface intersection number. -/
theorem IsClosedPointTower.classIntersectionNumber_pullback (hT : IsClosedPointTower X T)
    (a b : LineBundleClass X) :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    Chow.classIntersectionNumber k Y (pullback T.toBase a) (pullback T.toBase b) =
      Chow.classIntersectionNumber k X a b := by
  simpa only [picardMarking_apply, picardHom_apply_zero, toMul_ofMul, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, sub_zero] using
    (classIntersectionNumber_picardMarking k hT (Additive.ofMul a, 0) (Additive.ofMul b, 0))

end EulerCharacteristic

section CanonicalClass

variable [PerfectField k]

/-- In an ordered point-blowup marking the canonical class has the base canonical class
as its first coordinate and coefficient one at each total-transform exceptional divisor. -/
theorem picardMarking_canonicalClass [IsIntegral X] [IsNoetherian X]
    (hT : IsClosedPointTower X T) :
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      hT.smoothOfRelativeDimension f
    T.picardMarking hT f (Additive.ofMul (mk (canonicalBundle k X 2)), fun _ ↦ 1) =
      Additive.ofMul (mk (canonicalBundle k Y 2)) := by
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
  let : T.toBase.IsOver (Spec (.of k)) := ⟨rfl⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) := hT.smoothOfRelativeDimension f
  exact (T.picardMarking_apply hT f _).trans
    (congrArg Additive.ofMul (hT.mk_canonicalBundle_picardHom k).symm)

/-- The canonical complement of a pulled-back line bundle has the base canonical
complement as its first coordinate and coefficient one at each exceptional divisor
in the total-transform marking. -/
theorem canonical_complement_picardHom [IsIntegral X] [IsNoetherian X]
    (hT : IsClosedPointTower X T) (L : InvertibleSheaf X) :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) := hT.smoothOfRelativeDimension f
    let M := (InvertibleSheaf.pullback T.toBase).obj L
    mk (InvertibleSheaf.tensorProduct (canonicalBundle k Y 2) (InvertibleSheaf.dual M)) =
      (T.picardHom (Additive.ofMul (mk (InvertibleSheaf.tensorProduct (canonicalBundle k X 2)
        (InvertibleSheaf.dual L))), fun _ ↦ 1)).toMul := by
  intro _ _ M
  have hK := congrArg Additive.toMul (picardMarking_canonicalClass k hT)
  rw [T.picardMarking_apply, toMul_ofMul] at hK
  have hM : mk M = (T.picardHom (Additive.ofMul (mk L), 0)).toMul := by
    rw [picardHom_apply_zero, toMul_ofMul, pullback_mk]
  simp only [mk_tensorProduct, ← inv_mk]
  rw [← hK, hM, ← div_eq_mul_inv, ← toMul_sub, ← map_sub]
  simp only [Prod.mk_sub_mk, sub_zero]
  congr 2

end CanonicalClass

/-- Intersecting a marked class with the canonical class subtracts the sum of its
total exceptional coefficients from the canonical intersection on the base. -/
theorem IsClosedPointTower.classIntersectionNumber_picardHom_canonicalBundle
    [IsAlgClosed k] [IsIntegral X] [X.IsProjectiveOver k] (hT : IsClosedPointTower X T)
    (a : Additive (LineBundleClass X) × (Fin n → ℤ)) :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      hT.smoothOfRelativeDimension f
    Chow.classIntersectionNumber k Y (T.picardHom a).toMul (mk (canonicalBundle k Y 2)) =
      Chow.classIntersectionNumber k X a.1.toMul (mk (canonicalBundle k X 2)) -
        ∑ j, a.2 j := by
  let : IsNoetherian X := isNoetherian_of_finiteType f
  have h := classIntersectionNumber_picardMarking k hT a
    (Additive.ofMul (mk (canonicalBundle k X 2)), fun _ ↦ 1)
  dsimp only at h
  simpa only [picardMarking_canonicalClass, picardMarking_apply T hT f a,
    toMul_ofMul, mul_one] using h

/-- If two marked classes identify under an isomorphism of the resolved surfaces,
the change in anticanonical degree on their bases equals the change in the sum
of their orders. Each order is the negative of the total exceptional coefficient.
The two towers can have different lengths. -/
theorem IsClosedPointTower.classIntersectionNumber_canonicalBundle_sub_of_pullback_picardHom_eq
    [IsAlgClosed k] [IsIntegral X] [X.IsProjectiveOver k]
    {Z W : Scheme.{u}} {m : ℕ} {U : BlowupTower Z m W}
    [Z.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
    [IsIntegral Z] [Z.IsProjectiveOver k] (hT : IsClosedPointTower X T)
    (hU : IsClosedPointTower Z U) (e : Y ≅ W)
    (he : e.hom ≫ U.toBase ≫ (Z ↘ Spec (.of k)) = T.toBase ≫ f)
    (a : Additive (LineBundleClass X) × (Fin n → ℤ))
    (b : Additive (LineBundleClass Z) × (Fin m → ℤ))
    (hab : pullback e.hom (U.picardHom b).toMul = (T.picardHom a).toMul) :
    Chow.classIntersectionNumber k X a.1.toMul (mk (canonicalBundle k X 2)) -
        Chow.classIntersectionNumber k Z b.1.toMul (mk (canonicalBundle k Z 2)) =
      (∑ j, a.2 j) - ∑ j, b.2 j := by
  let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
  let : W.Over (Spec (.of k)) := ⟨U.toBase ≫ (Z ↘ Spec (.of k))⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) := hT.smoothOfRelativeDimension f
  let : SmoothOfRelativeDimension 2 (W ↘ Spec (.of k)) :=
    hU.smoothOfRelativeDimension (Z ↘ Spec (.of k))
  let : e.hom.IsOver (Spec (.of k)) := ⟨he⟩
  have h := Chow.classIntersectionNumber_pullback_of_isIso k e.hom
    (U.picardHom b).toMul (mk (canonicalBundle k W 2))
  rw [hab, pullback_mk, mk_pullback_canonicalBundle] at h
  rw [hT.classIntersectionNumber_picardHom_canonicalBundle k a,
    hU.classIntersectionNumber_picardHom_canonicalBundle k b] at h
  omega

/-- When a resolved elementary link preserves the resolved line class and replaces
the order at stage `j` by `b - m` at the first reverse center, the anticanonical
degree of the base line class changes by `b - 2 * m`. The remaining orders keep
their relative positions. The formula includes a zero pivot order and applies
regardless of the self-intersections of the two ruling sections. See
[Lutz, Proposition 8.11](https://arxiv.org/pdf/2005.05010v3#page=72). -/
theorem IsClosedPointTower.classIntersectionNumber_canonicalBundle_sub_of_elementaryTransform
    {k : Type u} [Field k] [IsAlgClosed k]
    {X X' Y Y' : Scheme.{u}} [X.Over (Spec (.of k))] [X'.Over (Spec (.of k))]
    [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 2 (X' ↘ Spec (.of k))]
    [IsIntegral X] [IsIntegral X'] [X.IsProjectiveOver k] [X'.IsProjectiveOver k]
    {n : ℕ} {T : BlowupTower X (n + 1) Y} {U : BlowupTower X' (1 + n) Y'}
    (hT : IsClosedPointTower X T) (hU : IsClosedPointTower X' U) (e : Y ≅ Y')
    (he : e.hom ≫ U.toBase ≫ (X' ↘ Spec (.of k)) = T.toBase ≫ (X ↘ Spec (.of k)))
    (a : Additive (LineBundleClass X)) (a' : Additive (LineBundleClass X'))
    (x : Fin (n + 1) → ℤ) (j : Fin (n + 1)) (b : ℤ)
    (hclass : pullback e.hom
      (U.picardHom (a', Fin.append (fun _ : Fin 1 ↦ -b - x j) (x ∘ j.succAbove))).toMul =
      (T.picardHom (a, x)).toMul) :
    Chow.classIntersectionNumber k X a.toMul (mk (canonicalBundle k X 2)) -
      Chow.classIntersectionNumber k X' a'.toMul (mk (canonicalBundle k X' 2)) =
      b + 2 * x j := by
  have h := hT.classIntersectionNumber_canonicalBundle_sub_of_pullback_picardHom_eq
    k hU e he _ _ hclass
  rw [Fin.sum_univ_succAbove x j] at h
  simp only [Fin.sum_univ_add, Fin.sum_univ_one, Fin.append_left, Fin.append_right,
    Function.comp_apply] at h
  omega

/-- A class pulled back from the base pairs trivially with the exceptional correction
to the canonical class of a closed-point blowup tower. -/
theorem IsClosedPointTower.classIntersectionNumber_pullback_canonicalBundle
    [IsAlgClosed k] [IsIntegral X] [X.IsProjectiveOver k] (hT : IsClosedPointTower X T)
    (a : LineBundleClass X) :
    let : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      hT.smoothOfRelativeDimension f
    Chow.classIntersectionNumber k Y (pullback T.toBase a) (mk (canonicalBundle k Y 2)) =
      Chow.classIntersectionNumber k X a (mk (canonicalBundle k X 2)) := by
  simpa only [picardHom_apply_zero, toMul_ofMul, Pi.zero_apply, Finset.sum_const_zero, sub_zero]
    using hT.classIntersectionNumber_picardHom_canonicalBundle k (Additive.ofMul a, 0)

/-- The canonical self-intersection falls by the length of a tower of point blowups. -/
theorem classIntersectionNumber_canonicalBundle [IsAlgClosed k] [IsIntegral X]
    [X.IsProjectiveOver k] (hT : IsClosedPointTower X T) :
    letI : Y.Over (Spec (.of k)) := ⟨T.toBase ≫ f⟩
    letI : SmoothOfRelativeDimension 2 (Y ↘ Spec (.of k)) :=
      hT.smoothOfRelativeDimension f
    Chow.classIntersectionNumber k Y (mk (canonicalBundle k Y 2)) (mk (canonicalBundle k Y 2)) =
      Chow.classIntersectionNumber k X (mk (canonicalBundle k X 2)) (mk (canonicalBundle k X 2)) -
        n := by
  have : IsNoetherian X := isNoetherian_of_finiteType f
  have h := hT.classIntersectionNumber_picardHom_canonicalBundle k
    (Additive.ofMul (mk (canonicalBundle k X 2)), fun _ ↦ 1)
  rw [← picardMarking_apply T hT f, picardMarking_canonicalClass] at h
  simpa only [toMul_ofMul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using h

end QPainleve.BlowupTower
