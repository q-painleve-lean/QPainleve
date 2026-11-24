/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.Picard.Hirzebruch
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.ElementaryTransform

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# Resolution transport across a toric Hirzebruch link

The toric elementary link transports the rest of a specified closed-point
resolution to the reverse corner without changing the subsequent exceptional
coefficients. When the selected multiplicity satisfies the degree-decrease
inequality, the transported resolution has strictly smaller Sarkisov bidegree.

This is the toric link in Lemma 8.9 and Proposition 8.11 of
[Lutz's appendix to Hacking and Keating][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory Module PointedCone
open QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

open TauCeti.Toric

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i}

local notation "X[" Δ "]" => Fan.algebraicRealization Δ
local notation "I[" σ "]" => Scheme.Hom.ker (Fan.distinguishedPointHom _ σ)
local notation "tower[" I "]" => BlowupTower.snoc BlowupTower.nil I
local notation "rays[" Δ "]" => Set.range (Fan.Ray.primitiveGenerator (Phi := Δ))

private theorem toricLink_bidegree_lt {n : ℕ} (β c : ℤ) (m : Fin n → ℤ)
    (hm : ∀ j, 0 ≤ -m j) (hbound : -c ≤ β) (hhigh : β < 2 * (-c)) :
    hirzebruchSarkisovBidegree β.toNat (β + c + ∑ j, -m j).toNat <
      hirzebruchSarkisovBidegree β.toNat (-c + ∑ j, -m j).toNat := by
  let orders : Fin (n + 1) → ℤ := Fin.cons (-c) (fun j ↦ -m j)
  have horders (j : Fin (n + 1)) : 0 ≤ orders j := by
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · have hc : 0 ≤ -c := by omega
      simpa [orders] using hc
    · simpa [orders] using hm k
  have h := hirzebruchSarkisovBidegree_elementaryTransform_lt (m := orders)
    0 horders (by simpa [orders] using hbound) (by simpa [orders] using hhigh)
  simpa only [orders, Fin.cons_zero, Fin.update_cons_zero, Fin.sum_univ_succ, Fin.cons_succ,
    sub_neg_eq_add] using h

/-- Transport a specified closed-point resolution beginning at a Hirzebruch toric
corner across its elementary link. The transported resolution starts at the reverse
corner. Each retained center is projected from the same point of the common blowup
on both sides of the link. The subsequent total exceptional coefficients retain
their order, including those at infinitely near points. If the original resolved
class has coefficients `(a, b, -m)` at the fiber, chosen section and first
exceptional class, its new coefficients are `(a + b - m, b, -(b - m))`.
The sum of base orders changes by `b - 2 * m`. For nonnegative orders with
`b / 2 < m ≤ b`, this gives a strict Sarkisov bidegree decrease. -/
theorem exists_hirzebruch_toric_link_resolution
    (b : Basis (Fin 2) ℤ N) (e : ℤ) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    (hrays : rays[Φ] = {b 0, b 1, -b 0, e • b 0 - b 1})
    (σ : Φ.cones) (hσ : σ.val = hull ℝ (Set.range (i ∘ b)))
    {n : ℕ} {Y : Scheme} {T : BlowupTower (I[σ]).blowup n Y}
    (hT : IsClosedPointTower (I[σ]).blowup T) :
    letI : Nonempty Φ.cones := hc.nonempty_cones
    ∃ (Ψ F : Fan i) (hΨ : Ψ.IsRegular) (_ : F.IsRegular)
      (hc' : Ψ.IsComplete) (_ : F.IsComplete) (d : Basis (Fin 2) ℤ N)
      (τ : Ψ.cones) (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
      (g : X[F] ≅ (I[σ]).blowup) (g' : X[F] ≅ (I[τ]).blowup)
      (r : Fin 4 ≃ Φ.Ray) (r' : Fin 4 ≃ Ψ.Ray)
      (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])
      (hr' : (fun j ↦ (r' j).primitiveGenerator) = ![d 0, d 1, -d 0, (e + 1) • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower (I[τ]).blowup n Z) (k : Y ≅ Z),
      let U' := (tower[I[τ]]).append U
      ∃ hU' : IsClosedPointTower X[Ψ] U',
      d 0 = b 0 ∧ d 1 = b 0 + b 1 ∧ τ.val = hull ℝ {i (d 1), i (-d 0)} ∧
      g.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap ∧
      g'.hom ≫ (I[τ]).blowupToBase = t.toFanHom.algebraicMap ∧
      k.hom ≫ U'.toBase = T.toBase ≫ g.inv ≫ t.toFanHom.algebraicMap ∧
      hU'.baseCenter (Fin.castAdd n (0 : Fin 1)) =
        Ψ.distinguishedPointHom τ (IsLocalRing.closedPoint ℂ) ∧
      (∀ j : Fin n,
        t.toFanHom.algebraicMap (g.inv (hT.baseCenter j)) = hU'.baseCenter (j.natAdd 1)) ∧
      letI : Nonempty Ψ.cones := hc'.nonempty_cones
      let C := Fan.hirzebruchPicardBasis b e hΦ r hr
      let C' := Fan.hirzebruchPicardBasis d (e + 1) hΨ r' hr'
      ∀ (α β c : ℤ) (m : Fin n → ℤ),
        let coeffs := Fin.append (fun _ : Fin 1 ↦ c) m
        let coeffs' := Fin.append (fun _ : Fin 1 ↦ -β - c) m
        let M := ∑ j, -coeffs j
        let M' := ∑ j, -coeffs' j
        pullback k.hom (U'.picardHom ((α + β + c) • C' 0 + β • C' 1, coeffs')).toMul =
          (((tower[I[σ]]).append T).picardHom (α • C 0 + β • C 1, coeffs)).toMul ∧
        M' = M + β + 2 * c ∧
        ((∀ j, 0 ≤ -m j) → -c ≤ β → β < 2 * (-c) →
          hirzebruchSarkisovBidegree β.toNat M'.toNat <
            hirzebruchSarkisovBidegree β.toNat M.toNat) := by
  obtain ⟨Ψ, F, hΨ, hF, hc', hcF, d, τ, s, t, g, g', r, r', hr, hr',
      hd₀, hd₁, hτcone, hg, hg', hcoord⟩ :=
    Fan.exists_hirzebruch_toric_elementary_transform_picard_coordinates b e hΦ hc hrays σ hσ
  let R := T.transport (g.symm ≪≫ g')
  let U := (tower[I[τ]]).append R.tower
  have hτ : IsClosedPointTower X[Ψ] (tower[I[τ]]) :=
    IsClosedPointTower.nil.snoc _ (Ψ.isClosed_singleton_distinguishedPoint τ)
      (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField
  let hR := R.isLift.isClosedPointTower hT
  let hU : IsClosedPointTower X[Ψ] U := hτ.append hR
  have hproj : R.iso.hom ≫ U.toBase = T.toBase ≫ g.inv ≫ t.toFanHom.algebraicMap := by
    rw [toBase_append, ← Category.assoc, R.isLift.hom_toBase, toBase_snoc, toBase_nil,
      Category.comp_id, Category.assoc, Iso.trans_hom, Iso.symm_hom, Category.assoc, hg']
  refine ⟨Ψ, F, hΨ, hF, hc', hcF, d, τ, s, t, g, g', r, r', hr, hr', _, R.tower, R.iso,
    hU, hd₀, hd₁, hτcone, hg, hg', hproj, ?_, ?_, fun α β c m ↦ ⟨?_, ?_, ?_⟩⟩
  · rw [baseCenter_append_castAdd hτ hR, baseCenter_snoc_nil,
      hτ.lastCenter_eq _ (Ψ.isClosed_singleton_distinguishedPoint τ)
        (Ψ.distinguishedPointHom τ).ker_eq_ker_fromSpecResidueField]
  · intro j
    rw [baseCenter_append_natAdd hτ hR, toBase_snoc, toBase_nil, Category.comp_id,
      ← R.isLift.hom_baseCenter hT hR]
    simp only [Iso.trans_hom, Iso.symm_hom, ← hg', Scheme.Hom.comp_apply]
  · rw [picardHom_append, picardHom_append, R.isLift.pullback_picardHom]
    simp only [Fin.append_left, Fin.append_right]
    have hfirst := congrArg (pullback g.inv) (hcoord α β c)
    simp only [pullback_comp, Iso.inv_hom_id, pullback_id] at hfirst
    rw [Iso.trans_hom, Iso.symm_hom, ← hfirst, ofMul_toMul]
  · simp only [Fin.sum_univ_add, Fin.sum_univ_one, Fin.append_left, Fin.append_right]
    omega
  · intro hm hbound hhigh
    simp only [Fin.sum_univ_add, Fin.sum_univ_one, Fin.append_left, Fin.append_right, neg_sub,
      sub_neg_eq_add, add_comm c β]
    exact toricLink_bidegree_lt β c m hm hbound hhigh

/-- A retained center that is first over its source point is first over its
target point as well, provided the common point projects into both isomorphism
loci and the reverse corner lies outside the target isomorphism locus. -/
theorem first_center_of_toric_link
    {Ψ F : Fan i} {σ : Φ.cones} {n : ℕ} {Y Z : Scheme}
    {T : BlowupTower (I[σ]).blowup n Y} (hT : IsClosedPointTower (I[σ]).blowup T)
    {U : BlowupTower X[Ψ] (1 + n) Z} (hU : IsClosedPointTower X[Ψ] U)
    (s : F.IsSubdivision Φ) (t : F.IsSubdivision Ψ)
    (v : X[F] ≅ (I[σ]).blowup)
    (hv : v.hom ≫ (I[σ]).blowupToBase = s.toFanHom.algebraicMap)
    (hcorner : hU.baseCenter (Fin.castAdd n (0 : Fin 1)) ∉ t.toFanHom.algebraicMap.isoLocus)
    (hretained : ∀ k : Fin n,
      t.toFanHom.algebraicMap (v.inv (hT.baseCenter k)) = hU.baseCenter (k.natAdd 1))
    {z : X[F]} (hs : s.toFanHom.algebraicMap z ∈ s.toFanHom.algebraicMap.isoLocus)
    (ht : t.toFanHom.algebraicMap z ∈ t.toFanHom.algebraicMap.isoLocus)
    (l : Fin n) (hl : (I[σ]).blowupToBase (hT.baseCenter l) = s.toFanHom.algebraicMap z)
    (hfirst : ∀ k < l, (I[σ]).blowupToBase (hT.baseCenter k) ≠ s.toFanHom.algebraicMap z) :
    hU.baseCenter (l.natAdd 1) = t.toFanHom.algebraicMap z ∧
      ∀ k < l.natAdd 1, hU.baseCenter k ≠ t.toFanHom.algebraicMap z := by
  have hsrc (k : Fin n) :=
    congrArg (fun f : X[F] ⟶ X[Φ] ↦ f (v.inv (hT.baseCenter k))) hv
  simp only [Scheme.Hom.comp_apply, Scheme.inv_hom_apply] at hsrc
  have hproj := (hsrc l).symm.trans hl
  have hpt : v.inv (hT.baseCenter l) = z := s.toFanHom.algebraicMap.injOn_preimage_isoLocus
    (by rwa [Set.mem_preimage, hproj]) hs hproj
  refine ⟨(hretained l).symm.trans (congrArg t.toFanHom.algebraicMap hpt), ?_⟩
  refine Fin.addCases ?_ ?_
  · intro k _ he
    rw [Subsingleton.elim k (0 : Fin 1)] at he
    exact hcorner (he ▸ ht)
  · intro k hk he
    have e := (hretained k).trans he
    have e' := t.toFanHom.algebraicMap.injOn_preimage_isoLocus
      (by rwa [Set.mem_preimage, e]) ht e
    exact hfirst k (by simpa only [Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hk)
      ((hsrc k).trans (congrArg s.toFanHom.algebraicMap e'))

end QPainleve.BlowupTower.IsClosedPointTower
