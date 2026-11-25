/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Inversion
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.PositiveSection.Corner

import Mathlib.Combinatorics.Quiver.Cast
import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization.Iso
import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch.Marking
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# Marked toric corner pivots on a common resolving surface

A toric pivot at a proper center on the positive section of a Hirzebruch
surface keeps the specified plane projection on the common resolving surface.
A first center on the contracted invariant fiber moves to the reverse center.
On the other fiber it stays first over its transported point. The new orders
bound the original marked orders, and the two invariant fibers are still distinct
in the frame of the new ruling.

The Picard coordinates use the elementary transformation of
[Lutz, Lemma 8.9][HKL]. The retained first centers are used in the
positive-section descent to a quadric.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=71
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.SymmetricAlgebra LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

open scoped Sarkisov

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "pt" => (IsLocalRing.closedPoint ℂ : S)
local notation "point[" j "]" => projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) j 0
local notation "baseMap[" t "]" =>
  ite (t = (0 : Fin 2)) (𝟙 (projectiveLine ℂ)) (Iso.hom (projectiveLine.coordinateSwap ℂ))
local notation "rankTwo[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "X[" Φ "]" => Fan.algebraicRealization Φ
local notation "f[" Φ "]" => (X[Φ] ↘ S)
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A
local notation "ruling[" Φ "," b "," e "," r "," hr "]" =>
  Fan.characterRuling Φ (LinearMap.toAddMonoidHom (Basis.coord b 1))
    (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)
local notation "line[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))

private theorem coordinatePoint_baseMap (t : Fin 2) :
    ∃ p : Equiv.Perm (Fin 2), ∀ a, (point[a] ≫ baseMap[t]) pt = point[p a] pt := by
  fin_cases t
  · exact ⟨Equiv.refl _, fun a ↦ by simp⟩
  · exact ⟨Fin.revPerm, fun a ↦ by simp⟩

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)] [PreirreducibleSpace X]
  {D : X.IdealSheafData} {n : ℕ} {ι : Type*}

private theorem exists_path_on_resolving_surface {A : LogarithmicProjection i D}
    {Y : Scheme} [Y.Over S] [SmoothOfRelativeDimension 2 (Y ↘ S)] [PreirreducibleSpace Y]
    (hRank : finrank ℤ N = 2) (k : X ≅ Y) [k.hom.IsOver S]
    {L R : LogarithmicProjection i (D.comap k.inv)}
    (hFan : L.fan = A.fan) (hHom : A.hom ≍ k.hom ≫ L.hom)
    (p : SarkisovPath L R) :
    ∃ C : LogarithmicProjection i D, Nonempty (SarkisovPath A C) ∧
      C.fan = R.fan ∧ C.hom ≍ k.hom ≫ R.hom := by
  have hE : (D.comap k.inv).comap k.hom = D := by simp [← comap_comp]
  let G := precomposeSarkisovOfIso (i := i) hRank k hE
  have hSrc : obj[G,L] = A := LogarithmicProjection.ext
    ((precomposeSarkisovOfIso_obj_fan hRank k hE L).trans hFan)
    ((precomposeSarkisovOfIso_obj_hom hRank k hE L).trans hHom.symm)
  exact ⟨obj[G,R], ⟨(G.mapPath p).cast hSrc rfl⟩,
    precomposeSarkisovOfIso_obj_fan hRank k hE R, precomposeSarkisovOfIso_obj_hom hRank k hE R⟩

private theorem exists_marked_centers_of_corner
    {Φ Ψ : Fan i} {Y Z : Scheme}
    {T : BlowupTower X[Φ] (n + 1) Y} (hT : IsClosedPointTower X[Φ] T)
    {U : BlowupTower X[Ψ] (1 + n) Z} (hU : IsClosedPointTower X[Ψ] U)
    (j : Fin (n + 1)) (hj : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (f q : X[Φ] ⟶ projectiveLine ℂ) (q' : X[Ψ] ⟶ projectiveLine ℂ)
    (t : Fin 2) (hq : q ≫ baseMap[t] = f)
    (x : Fin (n + 1) → ℤ) (y : Fin (1 + n) → ℤ)
    (c : Fin (n + 1) → ℤ) (c' : Fin (1 + n) → ℤ)
    (hcoeff : c' = Fin.append (0 : Fin 1 → ℤ) (c ∘ j.succAbove))
    (fiber : ι ↪ Fin 2) (index : ι → Fin (n + 1))
    (hfirst : ∀ a, ∀ l < index a, hT.baseCenter l ≠ hT.baseCenter (index a))
    (hvalue : ∀ a, f (hT.baseCenter (index a)) = point[fiber a] pt)
    (hpivot : ∀ a, index a ≠ j)
    (hretained : ∀ l : Fin n, hT.baseCenter (j.succAbove l) ≠ hT.baseCenter j →
      (∀ a < j.succAbove l, hT.baseCenter a ≠ hT.baseCenter (j.succAbove l)) →
      ∃ a : Fin (1 + n), (∀ k < a, hU.baseCenter k ≠ hU.baseCenter a) ∧
        q' (hU.baseCenter a) = q (hT.baseCenter (j.succAbove l)) ∧
        -x (j.succAbove l) ≤ -y a ∧
        (q (hT.baseCenter (j.succAbove l)) = q (hT.baseCenter j) → a = 0) ∧
        (q (hT.baseCenter (j.succAbove l)) ≠ q (hT.baseCenter j) →
          a = l.natAdd 1)) :
    ∃ (fiber' : ι ↪ Fin 2) (index' : ι → Fin (1 + n)),
      (∀ a, ∀ l < index' a, hU.baseCenter l ≠ hU.baseCenter (index' a)) ∧
      (∀ a, (q' ≫ baseMap[t]) (hU.baseCenter (index' a)) = point[fiber a] pt) ∧
      (∀ a, q' (hU.baseCenter (index' a)) = point[fiber' a] pt) ∧
      (∀ a, -x (index a) ≤ -y (index' a)) ∧
      ∀ a, c (index a) = 0 → c' (index' a) = 0 := by
  obtain ⟨p, hp⟩ := coordinatePoint_baseMap t
  let : IsIso baseMap[t] := by
    by_cases ht : t = 0 <;> simp only [ht, ite_true, ite_false] <;> infer_instance
  have hmarks (a : ι) : ∃ b : Fin (1 + n), (∀ l < b, hU.baseCenter l ≠ hU.baseCenter b) ∧
      (q' ≫ baseMap[t]) (hU.baseCenter b) = point[fiber a] pt ∧
      q' (hU.baseCenter b) = point[p.symm (fiber a)] pt ∧ -x (index a) ≤ -y b ∧
      (c (index a) = 0 → c' b = 0) := by
    have hpoint : hT.baseCenter (index a) ≠ hT.baseCenter j := by
      rcases lt_or_gt_of_ne (hpivot a) with h | h
      · exact hj _ h
      · exact (hfirst a _ h).symm
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq_iff.mpr (hpivot a)
    obtain ⟨b, hb, hval, horder, hsame, hdiff⟩ :=
      hretained l (hl.symm ▸ hpoint) (hl.symm ▸ hfirst a)
    have hv := calc
      (q' ≫ baseMap[t]) (hU.baseCenter b) = (q ≫ baseMap[t]) (hT.baseCenter (index a)) := by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hval, hl]
      _ = point[fiber a] pt := hq ▸ hvalue a
    have hp' := hp (p.symm (fiber a))
    rw [Equiv.apply_symm_apply] at hp'
    refine ⟨b, hb, hv, (baseMap[t]).injective ?_, hl ▸ horder, ?_⟩
    · exact ((Scheme.Hom.comp_apply _ _ _).symm.trans hv).trans
        (hp'.symm.trans (Scheme.Hom.comp_apply _ _ _))
    · intro hzero
      by_cases he : q (hT.baseCenter (j.succAbove l)) = q (hT.baseCenter j)
      · rw [hcoeff, hsame he]
        exact Fin.append_left _ _ (0 : Fin 1)
      · rw [hcoeff, hdiff he, Fin.append_right, Function.comp_apply, hl]
        exact hzero
  choose index' hfirst' hvals hvals' horder hoff using hmarks
  exact ⟨fiber.trans p.symm.toEmbedding, index', hfirst', hvals, hvals', horder, hoff⟩

/-- Resolve a proper corner pivot on either invariant fiber of the marked positive
section, keeping the specified plane morphism on the common resolving surface.
Each retained first center, distinct from the pivot, determines a first center
in the new tower with the same ruling value in the original frame and with
at least its original order. The retained centers may already lie at corners.
The reverse center misses the marked section, and each retained mark off the old
strict section stays off the new strict section. -/
theorem exists_marked_positive_section_corner_pivot
    (A : LogarithmicProjection i D) (b : Basis (Fin 2) ℤ N) (e : ℕ) (he : 0 < e)
    (r : Fin 4 ≃ A.fan.Ray)
    (hr : (fun l ↦ (r l).primitiveGenerator) = ![b 0, b 1, -b 0, (e : ℤ) • b 0 - b 1])
    {Y : Scheme} {T : BlowupTower X[A.fan] (n + 1) Y}
    (hT : IsClosedPointTower X[A.fan] T)
    (k : X ≅ Y) (hA : A.hom = k.hom ≫ T.toBase)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[A.fan])
    (hbir : Scheme.BirationalOver g (𝟙 P))
    (σ : A.fan.cones) (hσ : Nat.card (ToricRay σ.val) = 2) (hsec : (r 2).toCone ≤ σ)
    (j : Fin (n + 1)) (hp : A.fan.distinguishedPointHom σ pt = hT.baseCenter j)
    (hj : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (fiber : ι ↪ Fin 2) (index : ι → Fin (n + 1))
    (hfirst : ∀ a, ∀ l < index a, hT.baseCenter l ≠ hT.baseCenter (index a))
    (hvalue : ∀ a, ruling[A.fan,b,e,r,hr] (hT.baseCenter (index a)) = point[fiber a] pt)
    (hpivot : ∀ a, index a ≠ j) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[A.fan] :=
      rankTwo[b] ▸ A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
    let : IsNoetherian X[A.fan] := by
      let : Smooth f[A.fan] := SmoothOfRelativeDimension.smooth 2 _
      exact isNoetherian_of_finiteType f[A.fan]
    let x := line[T,hT,f[A.fan],g]
    let C₀ := A.fan.hirzebruchPicardBasis b (e : ℤ) A.isRegular r hr
    ∃ (C : LogarithmicProjection i D) (t : Fin 2)
      (d : Basis (Fin 2) ℤ N) (s : Fin 4 ≃ C.fan.Ray)
      (hs : (fun l ↦ (s l).primitiveGenerator) =
        ![d 0, d 1, -d 0, ((e - 1 : ℕ) : ℤ) • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower X[C.fan] (1 + n) Z)
      (hU : IsClosedPointTower X[C.fan] U) (k' : X ≅ Z) (g' : Z ⟶ P)
      (fiber' : ι ↪ Fin 2) (index' : ι → Fin (1 + n)),
      Nonempty (SarkisovPath A C) ∧ C.hom = k'.hom ≫ U.toBase ∧ k'.hom ≫ g' = k.hom ≫ g ∧
      g' ≫ (P ↘ S) = U.toBase ≫ f[C.fan] ∧ Scheme.BirationalOver g' (𝟙 P) ∧
      let : Nonempty C.fan.cones := C.isComplete.nonempty_cones
      let : SmoothOfRelativeDimension 2 f[C.fan] :=
        rankTwo[b] ▸ C.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap C.isRegular
      let : IsNoetherian X[C.fan] := by
        let : Smooth f[C.fan] := SmoothOfRelativeDimension.smooth 2 _
        exact isNoetherian_of_finiteType f[C.fan]
      let y := line[U,hU,f[C.fan],g']
      let C₁ := C.fan.hirzebruchPicardBasis d ((e - 1 : ℕ) : ℤ) C.isRegular s hs
      C₁.repr y.1 0 = C₀.repr x.1 0 + x.2 j ∧ C₁.repr y.1 1 = C₀.repr x.1 1 ∧
      y.2 = Fin.append (fun _ : Fin 1 ↦ -C₀.repr x.1 1 - x.2 j) (x.2 ∘ j.succAbove) ∧
      let c := hT.strictTransformCoefficients (A.fan.rayBoundaryIdeal A.isRegular (r 2))
      let c' := hU.strictTransformCoefficients (C.fan.rayBoundaryIdeal C.isRegular (s 2))
      c' = Fin.append (0 : Fin 1 → ℤ) (c ∘ j.succAbove) ∧
      (∀ a, ∀ l < index' a, hU.baseCenter l ≠ hU.baseCenter (index' a)) ∧
      (∀ a, (ruling[C.fan,d,(e - 1 : ℕ),s,hs] ≫ baseMap[t])
        (hU.baseCenter (index' a)) = point[fiber a] pt) ∧
      (∀ a, ruling[C.fan,d,(e - 1 : ℕ),s,hs] (hU.baseCenter (index' a)) = point[fiber' a] pt) ∧
      (∀ a, -x.2 (index a) ≤ -y.2 (index' a)) ∧
      ∀ a, c (index a) = 0 → c' (index' a) = 0 := by
  intro hcones hdim hnoeth x C₀
  let := hcones
  let := hdim
  let := hnoeth
  let : Smooth f[A.fan] := SmoothOfRelativeDimension.smooth 2 _
  let : X[A.fan].IsProjectiveOver ℂ :=
    A.fan.isProjectiveOver_algebraicRealization_of_isComplete A.isRegular A.isComplete b
  let : Y.Over S := ⟨T.toBase ≫ f[A.fan]⟩
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[A.fan]
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral Y := hT.isIntegral f[A.fan]
  let : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f[A.fan]
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase f[A.fan]).symm.trans
    (hA ▸ comp_over A.hom S)⟩
  obtain ⟨t, b₀, r₀, hr₀, hcorner, -, -, hsection, hPic, hRuling⟩ :=
    A.fan.exists_hirzebruch_section_corner_picardBasis_ruling b (e : ℤ) r hr
      A.isRegular A.isComplete σ hσ hsec
  let E := D.comap k.inv
  have hPole : (A.fan.boundaryIdeal A.isComplete.nonempty_cones).comap T.toBase =
      E * ramificationIdealSheaf ℂ T.toBase := by
    have h := comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso ℂ k.hom T.toBase 2
      (D := A.fan.boundaryIdeal A.isComplete.nonempty_cones) (Q := D)
    rw [IsIso.inv_eq_of_hom_inv_id k.hom_inv_id] at h
    exact h.mp (by simpa only [hA] using A.comap_boundaryIdeal)
  -- Perform the link in tower coordinates and put its path back on the prescribed surface.
  obtain ⟨R, p, d, s, hs, Z, U, hU, k₀, -, -, hR, -, hg', hbir', -, ha, hβ, horders,
      -, -, -, hcoeff, hretained⟩ :=
    hT.exists_sarkisov_path_of_positive_corner b₀ e he A.isRegular A.isComplete r₀ hr₀ g hg hbir
      σ hcorner j hp.symm hj E hPole
  let L : LogarithmicProjection i E :=
    ⟨A.fan, A.isRegular, A.isComplete, T.toBase, inferInstance, inferInstance, hPole⟩
  obtain ⟨C, ⟨q⟩, hCfan, hChom⟩ :=
    exists_path_on_resolving_surface rankTwo[b] k (L := L) rfl (heq_of_eq hA) p
  rcases C with ⟨Φ, hΦ, hc, l, hlover, hldom, hlog⟩
  dsimp only at hCfan hChom
  subst Φ
  let C : LogarithmicProjection i D := ⟨R.fan, hΦ, hc, l, hlover, hldom, hlog⟩
  -- Apply the same frame change to every retained mark, keeping its position off the section.
  have hcoeff' := hsection ▸ hcoeff
  obtain ⟨fiber', index', hfirst', hval, hvals, hbound, hoff⟩ :=
    exists_marked_centers_of_corner hT hU j hj _ _ _ t hRuling _ _ _ _ hcoeff' fiber index
      hfirst hvalue hpivot (fun l hl hlf ↦ by
        obtain ⟨a, ha, hv, ho, hs, hd⟩ := hretained l hl hlf
        exact ⟨a, ha, hv, ho, hs, fun he ↦ (hd he).1⟩)
  refine ⟨C, t, d, s, hs, Z, U, hU, k ≪≫ k₀, k₀.inv ≫ g, fiber', index', ⟨q⟩, ?_,
    by simp, hg', hbir', ?_, ?_, ?_, hcoeff', hfirst', hval, hvals, hbound, hoff⟩
  · exact eq_of_heq (by simpa only [C, hR, Category.assoc, Iso.trans_hom] using hChom)
  · simpa only [hPic] using ha
  · simpa only [hPic] using hβ
  · simpa only [hPic] using horders

end TauCeti.Toric.Fan.LogarithmicProjection
