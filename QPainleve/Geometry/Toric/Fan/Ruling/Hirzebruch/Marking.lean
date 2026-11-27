/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Negation

/-!
# Marking either invariant fiber of a Hirzebruch ruling

A toric elementary transformation at a section corner uses coordinates
placing the corner's fiber first. The Picard basis and the section rays
stay fixed under this change of marking. The ruling to the original
projective line is recovered by swapping its coordinates when the second
fiber is chosen. This lets projected blowup centers be tracked in the same
base coordinates through successive links.
-/

public section

open CategoryTheory Module PointedCone TauCeti.AlgebraicGeometry

namespace TauCeti.Toric.Fan

variable (k₀ : Type) [Field k₀]

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Basis (Fin 2) ℤ N) (e : ℤ)
  (r : Fin 4 ≃ Φ.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, e • b 0 - b 1])

local notation "fiber[" t "]" => (![1, 3] : Fin 2 → Fin 4) t
local notation "ruling[" b "," r "," h "]" =>
  Φ.characterRuling k₀ (LinearMap.toAddMonoidHom (Basis.coord b 1))
    (nonneg_or_nonpos_hirzebruch_ruling_character b e r h)
local notation "baseMap[" t "]" =>
  ite (t = (0 : Fin 2)) (𝟙 (projectiveLine k₀)) (Iso.hom (projectiveLine.coordinateSwap k₀))

include hr in
/-- Either invariant fiber can be placed first while keeping the section rays and
Picard basis fixed. Swapping the base coordinates when the second fiber is chosen
recovers the original ruling. -/
theorem exists_hirzebruch_picardBasis_ruling_of_fiber [Nonempty Φ.cones]
    (hΦ : Φ.IsRegular) (t : Fin 2) :
    ∃ (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ Φ.Ray)
      (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, e • d 0 - d 1]),
      s 0 = r 0 ∧ s 1 = r fiber[t] ∧ s 2 = r 2 ∧
        hirzebruchPicardBasis k₀ d e hΦ s hs = hirzebruchPicardBasis k₀ b e hΦ r hr ∧
        ruling[d,s,hs] ≫ baseMap[t] = ruling[b,r,hr] := by
  fin_cases t
  · exact ⟨b, r, hr, rfl, rfl, rfl, rfl, by simp⟩
  obtain ⟨d, s, hs, h₀, h₁, hPic⟩ := exists_hirzebruch_picardBasis_of_fiber k₀ b e r hr hΦ 1
  have hd₀ : d 0 = b 0 := (congrFun hs 0).symm.trans ((congrArg Ray.primitiveGenerator h₀).trans
    (congrFun hr 0))
  have hd₁ : d 1 = e • b 0 - b 1 :=
    (congrFun hs 1).symm.trans ((congrArg Ray.primitiveGenerator h₁).trans (congrFun hr 3))
  have h₂ : s 2 = r 2 := Ray.primitiveGenerator_injective
    ((congrFun hs 2).trans ((congrArg Neg.neg hd₀).trans (congrFun hr 2).symm))
  refine ⟨d, s, hs, h₀, h₁, h₂, hPic, ?_⟩
  have hcoord : d.coord 1 = -b.coord 1 := by
    have hb₀ : b.coord 1 (d 0) = 0 := by simp [hd₀, Basis.coord_apply]
    have hb₁ : b.coord 1 (d 1) = -1 := by simp [hd₁, Basis.coord_apply]
    apply d.ext
    intro j
    fin_cases j <;> simp [hb₀, hb₁, Basis.coord_apply]
  have hneg : (d.coord 1).toAddMonoidHom = -(b.coord 1).toAddMonoidHom := by
    ext x
    simp [hcoord]
  have hsign := hneg ▸ nonneg_or_nonpos_hirzebruch_ruling_character d e s hs
  have heq : ruling[d,s,hs] = Φ.characterRuling k₀ (-(b.coord 1).toAddMonoidHom) hsign := by
    congr 1
  rw [heq, Φ.characterRuling_neg k₀ _ (nonneg_or_nonpos_hirzebruch_ruling_character b e r hr) hsign]
  simp

include hr in
/-- A corner on the section numbered two admits a marking with that corner on the
first invariant fiber. The Picard basis and the marked section stay fixed, and the
base-coordinate comparison records which of the two original fibers was chosen. -/
theorem exists_hirzebruch_section_corner_picardBasis_ruling
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (σ : Φ.cones)
    (hσ : Nat.card (ToricRay σ.val) = 2) (hsec : (r 2).toCone ≤ σ) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    ∃ (t : Fin 2) (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ Φ.Ray)
      (hs : (fun j ↦ (s j).primitiveGenerator) = ![d 0, d 1, -d 0, e • d 0 - d 1]),
      σ.val = hull ℝ {i (-d 0), i (d 1)} ∧ s 0 = r 0 ∧ s 1 = r fiber[t] ∧ s 2 = r 2 ∧
        hirzebruchPicardBasis k₀ d e hΦ s hs = hirzebruchPicardBasis k₀ b e hΦ r hr ∧
        ruling[d,s,hs] ≫ baseMap[t] = ruling[b,r,hr] := by
  let : Nonempty Φ.cones := hc.nonempty_cones
  obtain ⟨t, hcorner⟩ := exists_hirzebruch_corner_eq_hull_of_section_le b e r hr hΦ hc σ hσ 1 hsec
  obtain ⟨d, s, hs, h₀, h₁, h₂, hPic, hRuling⟩ :=
    exists_hirzebruch_picardBasis_ruling_of_fiber k₀ b e r hr hΦ t
  refine ⟨t, d, s, hs, ?_, h₀, h₁, h₂, hPic, hRuling⟩
  have hsecGen : (s 2).primitiveGenerator = -d 0 := congrFun hs 2
  have hfibGen : (s 1).primitiveGenerator = d 1 := congrFun hs 1
  simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, ← h₁, ← h₂, hsecGen, hfibGen] using hcorner

end TauCeti.Toric.Fan
