/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.Incidence
public import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Picard
public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.Geometry.Toric.Fan.Picard.Hirzebruch
public import QPainleve.Geometry.Toric.Fan.Ruling.Hirzebruch

import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization.Iso
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.SarkisovDegree.ResolvedSection

/-!
# Marked positive-section pivots at smooth centers

A smooth pivot on the positive section lowers the Hirzebruch index on the
common resolving surface. It carries the specified map to the plane and the
remaining marked first centers. This is the smooth elementary transformation
in the preparation of the quadric in Lutz's [Proposition 8.11][HKL].

[HKL]: https://arxiv.org/abs/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

open scoped Sarkisov

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "f[" A "]" => Fan.algebraicRealization (LogarithmicProjection.fan A) ↘ S
local notation "rankTwo[" b "]" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "point" => (IsLocalRing.closedPoint ℂ : S)
local notation "coordPoint[" t "]" =>
  projectiveLine.polynomialPoint ℂ (RingHom.id ℂ) t 0 point
local notation "center[" b "," ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo[b] (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c point
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A
local notation "coords[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))
local notation "ruling[" A "," b "," e "," r "," hr "]" =>
  Fan.characterRuling (LogarithmicProjection.fan A) (LinearMap.toAddMonoidHom (Basis.coord b 1))
    (Fan.nonneg_or_nonpos_hirzebruch_ruling_character b e r hr)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X Y : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [PreirreducibleSpace X] {D : X.IdealSheafData} (A : LogarithmicProjection i D)
  (b : Basis (Fin 2) ℤ N) {n e : ℕ}
  (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, ((e + 1 : ℕ) : ℤ) • b 0 - b 1])

/-- A proper smooth pivot on the positive section gives a resolved path from the
specified projection to a marked Hirzebruch model of index one less. The ruling
degree and the map to the plane are preserved. The reverse center lies off the
strict positive section and all other stages retain their section incidence and
orders. Each marked invariant-fiber center stays first over its point, on the
same ruling value and off the transported section, at its reindexed stage. -/
theorem exists_sarkisov_path_of_marked_positive_section_smooth_center
    {T : BlowupTower A.fan.algebraicRealization (n + 1) Y}
    (hT : IsClosedPointTower A.fan.algebraicRealization T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f[A])
    (hbir : Scheme.BirationalOver g (𝟙 P))
    (u : X ≅ Y) (hA : A.hom = u.hom ≫ T.toBase)
    (j : Fin (n + 1)) (hfirst : ∀ l < j, hT.baseCenter l ≠ hT.baseCenter j)
    (c : ℂˣ) (hc : hT.baseCenter j = center[b,r 2,c])
    {ι : Type*} (fiber : ι → Fin 2) (mark : ι → Fin (n + 1)) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 f[A] :=
      rankTwo[b] ▸ A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular
    let : IsNoetherian A.fan.algebraicRealization := by
      let : Smooth f[A] := SmoothOfRelativeDimension.smooth 2 _
      exact isNoetherian_of_finiteType f[A]
    let x := coords[T,hT,f[A],g]
    let basis := A.fan.hirzebruchPicardBasis b (e + 1 : ℕ) A.isRegular r hr
    let sectionCenters := hT.strictTransformCenterIndices (A.fan.rayBoundaryIdeal A.isRegular (r 2))
    j ∈ sectionCenters →
    (∀ a, (∀ l < mark a, hT.baseCenter l ≠ hT.baseCenter (mark a)) ∧
      ruling[A,b,(e + 1 : ℕ),r,hr] (hT.baseCenter (mark a)) = coordPoint[fiber a] ∧
      mark a ∉ sectionCenters) →
    ∃ (C : LogarithmicProjection i D) (_ : SarkisovPath A C)
      (d : Basis (Fin 2) ℤ N) (t : Fin 4 ≃ C.fan.Ray)
      (ht : (fun l ↦ (t l).primitiveGenerator) = ![d 0, d 1, -d 0, (e : ℤ) • d 0 - d 1])
      (Z : Scheme) (U : BlowupTower C.fan.algebraicRealization (1 + n) Z)
      (hU : IsClosedPointTower C.fan.algebraicRealization U) (k : Y ≅ Z) (index : ι → Fin (1 + n)),
      C.hom = (u ≪≫ k).hom ≫ U.toBase ∧
      (k.inv ≫ g) ≫ (P ↘ S) = U.toBase ≫ f[C] ∧
      Scheme.BirationalOver (k.inv ≫ g) (𝟙 P) ∧
      let : Nonempty C.fan.cones := C.isComplete.nonempty_cones
      let : SmoothOfRelativeDimension 2 f[C] :=
        rankTwo[d] ▸ C.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap C.isRegular
      let : IsNoetherian C.fan.algebraicRealization := by
        let : Smooth f[C] := SmoothOfRelativeDimension.smooth 2 _
        exact isNoetherian_of_finiteType f[C]
      let y := coords[U,hU,f[C],k.inv ≫ g]
      let basis' := C.fan.hirzebruchPicardBasis d e C.isRegular t ht
      let sectionCenters' :=
        hU.strictTransformCenterIndices (C.fan.rayBoundaryIdeal C.isRegular (t 2))
      basis'.repr y.1 1 = basis.repr x.1 1 ∧ basis'.repr y.1 0 = basis.repr x.1 0 + x.2 j ∧
      y.2 = Fin.addCases (fun _ : Fin 1 ↦ -basis.repr x.1 1 - x.2 j) (x.2 ∘ j.succAbove) ∧
      sectionCenters' =
        (Finset.univ.filter fun l : Fin n ↦ j.succAbove l ∈ sectionCenters).map (Fin.natAddEmb 1) ∧
      ∀ a, (∃ l : Fin n, j.succAbove l = mark a ∧ index a = l.natAdd 1) ∧
        (∀ l < index a, hU.baseCenter l ≠ hU.baseCenter (index a)) ∧
        ruling[C,d,e,t,ht] (hU.baseCenter (index a)) = coordPoint[fiber a] ∧
        index a ∉ sectionCenters' ∧ y.2 (index a) = x.2 (mark a) := by
  intro hcones hdim hNoeth x basis sectionCenters hj hmarks
  let := hcones
  let := hdim
  let := hNoeth
  let : Y.Over S := ⟨T.toBase ≫ f[A]⟩
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension f[A]
  let : Smooth (X ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral Y := hT.isIntegral f[A]
  let : A.fan.algebraicRealization.IsProjectiveOver ℂ :=
    A.fan.isProjectiveOver_algebraicRealization_of_isComplete A.isRegular A.isComplete b
  let : T.toBase.IsOver S := ⟨rfl⟩
  let : u.hom.IsOver S := ⟨(Category.assoc _ _ _).symm.trans (hA ▸ comp_over A.hom S)⟩
  let E := D.comap u.inv
  have hpole : (A.fan.boundaryIdeal A.isComplete.nonempty_cones).comap T.toBase =
      E * hT.ramificationIdealSheafToBase ℂ := by
    rw [hT.ramificationIdealSheafToBase_def ℂ]
    have h := comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso ℂ u.hom T.toBase 2
      (D := A.fan.boundaryIdeal A.isComplete.nonempty_cones) (Q := D)
    rw [IsIso.inv_eq_of_hom_inv_id u.hom_inv_id] at h
    exact h.mp (by simpa only [hA] using A.comap_boundaryIdeal)
  have hlink := hT.exists_sarkisov_path_of_smooth_section b (e + 1) A.isRegular A.isComplete
    r hr 1 g hg hbir c j hc hfirst E hpole
  -- The pivot is on the second section, so the signed target index is nonnegative.
  have hsign : decide ((1 : Fin 2) = 0) = false := by decide
  dsimp only at hlink
  simp only [hsign, Bool.false_eq_true, ite_false, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right, Int.natAbs_natCast, Int.natCast_nonneg, true_implies, add_zero] at hlink
  obtain ⟨_, Z, U, hU, k, d, t, ht, hg', hbir', _, ⟨L, R, p, hL, hLhom, hR, hRhom, -, -⟩,
    htEq, -, -, hsection, hRuling, hcoef, hdegree, horders, -⟩ := hlink
  -- Return the path to the original common surface and identify its initial projection.
  have hDE : E.comap u.hom = D := by
    simp only [E, ← comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  let F := precomposeSarkisovOfIso (i := i) rankTwo[b] u hDE
  have hsource : obj[F,L] = A := by
    refine LogarithmicProjection.ext ((precomposeSarkisovOfIso_obj_fan ..).trans hL) ?_
    exact (precomposeSarkisovOfIso_obj_hom ..).trans
      ((heq_comp rfl rfl (congrArg Fan.algebraicRealization hL) HEq.rfl hLhom).trans
        (heq_of_eq hA.symm))
  have htargetFan : obj[F,R].fan = _ := (precomposeSarkisovOfIso_obj_fan ..).trans hR
  have htargetHom := (precomposeSarkisovOfIso_obj_hom rankTwo[b] u hDE R).trans
    (heq_comp rfl rfl (congrArg Fan.algebraicRealization hR) HEq.rfl hRhom)
  have hpath : SarkisovPath A obj[F,R] :=
    Eq.mp (congrArg (fun L' ↦ SarkisovPath L' obj[F,R]) hsource) (F.mapPath p)
  generalize obj[F,R] = C at htargetFan htargetHom hpath
  rcases C with ⟨Δ, hreg, hcomplete, h, hover, hdom, hboundary⟩
  dsimp only at htargetFan htargetHom
  subst Δ
  let C : LogarithmicProjection i D := ⟨_, hreg, hcomplete, h, hover, hdom, hboundary⟩
  have htarget : h = (u ≪≫ k).hom ≫ U.toBase := by
    simpa only [Iso.trans_hom, Category.assoc] using eq_of_heq htargetHom
  have hex (a : ι) : ∃ l, j.succAbove l = mark a :=
    Fin.exists_succAbove_eq_iff.mpr (fun eq ↦ (hmarks a).2.2 (eq.symm ▸ hj))
  choose l hl using hex
  refine ⟨C, hpath, d, t, ht, Z, U, hU, k, fun a ↦ (l a).natAdd 1, htarget, hg', hbir', ?_⟩
  intro _ _ _ y basis' sectionCenters'
  have ht' := congrArg (fun s : Fin 4 ≃ C.fan.Ray ↦ s 2) htEq
  have hsec :
      sectionCenters' =
        (Finset.univ.filter fun l : Fin n ↦ j.succAbove l ∈ sectionCenters).map
          (Fin.natAddEmb 1) := by
    have hsectionRay : (![0, 2] : Fin 2 → Fin 4) 1 = 2 := by decide
    simpa only [sectionCenters', sectionCenters, C, ht', Equiv.trans_apply, hsectionRay]
      using hsection
  refine ⟨hdegree, hcoef, horders, hsec, ?_⟩
  intro a
  obtain ⟨hfirstMark, hvalue, hoff⟩ := hmarks a
  have hfirstRetained : ∀ m < j.succAbove (l a),
      hT.baseCenter m ≠ hT.baseCenter (j.succAbove (l a)) := by
    simpa only [hl] using hfirstMark
  obtain ⟨hvalue', hfirst'⟩ := hRuling (l a) (fiber a) (by simpa only [hl] using hvalue)
  refine ⟨⟨l a, hl a, rfl⟩, hfirst' hfirstRetained, hvalue', ?_, ?_⟩
  · simpa only [hsec, ← Fin.natAddEmb_apply, Finset.mem_map', Finset.mem_filter, Finset.mem_univ,
      true_and, hl] using hoff
  · have hh := congrFun horders ((l a).natAdd 1)
    simpa only [Fin.addCases_right, Function.comp_apply, hl] using hh

end TauCeti.Toric.Fan.LogarithmicProjection
