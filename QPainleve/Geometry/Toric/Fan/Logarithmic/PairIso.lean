/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.StarFactorization

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition

/-!
# Logarithmic toric projections across a pair isomorphism

Two specified toric contractions on nodal models of isomorphic pairs can be read
on one resolving surface. The projections to the original pairs recover the
specified isomorphism, and both toric projections have the same pole ideal.
This supplies the common source when applying the factorization in
[Lutz's Theorem 8.4][HKL] to a map induced by an isomorphism of pairs.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=68
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

universe u

variable {K : Type u} [Field K] [PerfectField K]

local notation "S" => Spec (CommRingCat.of K)
local notation "Total[" D "," T "]" =>
  Scheme.IdealSheafData.radical (Scheme.IdealSheafData.comap D (BlowupTower.toBase T))

variable {N V N' V' : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'}
  {X Y X' Y' : Scheme} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
  [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of K))] [SmoothOfRelativeDimension 2 (Y ↘ Spec (.of K))]
  {D : X.IdealSheafData} {E : Y.IdealSheafData}
  {m n : ℕ} {T : BlowupTower X m X'} {U : BlowupTower Y n Y'}

/-- Given an isomorphism of pairs and specified logarithmic toric contractions on
their nodal models, the two towers have extensions on which the contractions are
logarithmic modifications with one common pole ideal. The two maps to the
original pairs differ by exactly the given isomorphism. The fans and the
morphisms of both contractions are retained. -/
theorem exists_common_logarithmic_projections_of_pair_iso
    (hN : Module.finrank ℤ N = 2) (hN' : Module.finrank ℤ N' = 2)
    (hD : D.IsEffectiveCartier) (hE : E.IsEffectiveCartier)
    (hDnode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hEnode : AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ Y ↘ S))
    (hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T)
    (hU : IsNodalBoundaryTower E (Y ↘ S) (𝟙 Y) U)
    (e : X ≅ Y) (he : e.hom ≫ Y ↘ S = X ↘ S) (heD : E.comap e.hom = D) :
    letI : X'.Over S := ⟨T.toBase ≫ X ↘ S⟩
    letI : Y'.Over S := ⟨U.toBase ≫ Y ↘ S⟩
    letI : SmoothOfRelativeDimension 2 (X' ↘ S) :=
      hT.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
    letI : SmoothOfRelativeDimension 2 (Y' ↘ S) :=
      hU.isClosedPointTower.smoothOfRelativeDimension (Y ↘ S)
    ∀ (A : LogarithmicProjection K i Total[D,T]) (B : LogarithmicProjection K i' Total[E,U]),
      IsModification A.hom → IsModification B.hom →
      ∃ (a b : ℕ) (W Z : Scheme) (L : BlowupTower X' a W) (R : BlowupTower Y' b Z) (f : W ≅ Z)
        (hTL : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) (T.append L))
        (_ : IsNodalBoundaryTower E (Y ↘ S) (𝟙 Y) (U.append R)),
        (T.append L).toBase ≫ e.hom = f.hom ≫ (U.append R).toBase ∧
        letI : W.Over S := ⟨(T.append L).toBase ≫ X ↘ S⟩
        letI : SmoothOfRelativeDimension 2 (W ↘ S) :=
          hTL.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
        ∃ (A' : LogarithmicProjection K i Total[D,T.append L])
          (B' : LogarithmicProjection K i' Total[D,T.append L]),
          A'.fan = A.fan ∧ A'.hom ≍ L.toBase ≫ A.hom ∧ IsModification A'.hom ∧
          B'.fan = B.fan ∧ B'.hom ≍ f.hom ≫ R.toBase ≫ B.hom ∧ IsModification B'.hom := by
  intro A B hA hB
  let : X'.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : Y'.Over S := ⟨U.toBase ≫ Y ↘ S⟩
  let : SmoothOfRelativeDimension 2 (X' ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
  let : SmoothOfRelativeDimension 2 (Y' ↘ S) :=
    hU.isClosedPointTower.smoothOfRelativeDimension (Y ↘ S)
  obtain ⟨a, b, W, Z, L, R, f, -, -, hL, hR, hf⟩ :=
    hT.exists_common_refinement_of_pair_iso hU e he
      (congrArg (fun I : X.IdealSheafData ↦ I.support) heD)
  have hTL := hT.append (hL.congr (by rw [Category.comp_id]) (by rw [Category.comp_id]))
  have hUR := hU.append (hR.congr (by rw [Category.comp_id]) (by rw [Category.comp_id]))
  have hbase : (T.append L).toBase ≫ e.hom = f.hom ≫ (U.append R).toBase := by
    simpa only [toBase_append, Category.assoc] using hf
  refine ⟨a, b, W, Z, L, R, f, hTL, hUR, hbase, ?_⟩
  let : W.Over S := ⟨(T.append L).toBase ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (W ↘ S) :=
    hTL.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
  let g := f.hom ≫ R.toBase
  have hLo : L.toBase ≫ T.toBase ≫ X ↘ S = W ↘ S := by
    rw [← Category.assoc, ← toBase_append]
    rfl
  have hRo : f.hom ≫ R.toBase ≫ U.toBase ≫ Y ↘ S = W ↘ S := by
    rw [← Category.assoc R.toBase, ← toBase_append, ← reassoc_of% hbase, he]
    rfl
  have hleft : L.toBase.IsOver S := ⟨hLo⟩
  have hright : g.IsOver S := ⟨(Category.assoc ..).trans hRo⟩
  have hLeftPole :=
    hT.comap_radical_comap_eq_mul_ramificationIdealSheaf hL hD hDnode (Iso.refl W)
      (by simpa only [Iso.refl_hom, Category.id_comp] using hLo)
  simp only [Iso.refl_hom, Category.id_comp, ← toBase_append] at hLeftPole
  have hRightPole :=
    hU.comap_radical_comap_eq_mul_ramificationIdealSheaf hR hE hEnode f hRo
  have htotal : E.comap (g ≫ U.toBase) = D.comap (T.append L).toBase := by
    dsimp only [g]
    rw [Category.assoc, ← toBase_append, ← hbase, comap_comp, heD]
  dsimp only at hRightPole
  rw [htotal] at hRightPole
  let : IsIntegral X' := hT.isClosedPointTower.isIntegral (X ↘ S)
  let : IsIntegral Y' := hU.isClosedPointTower.isIntegral (Y ↘ S)
  let : IsModification L.toBase :=
    hL.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (X' ↘ S)
  let : IsModification R.toBase :=
    hR.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Y' ↘ S)
  let : IsModification f.hom := IsModification.of_isIso _
  let : IsModification g := IsModification.comp f.hom R.toBase
  exact ⟨LogarithmicProjection.precomposeProjection hN L.toBase hLeftPole A,
    LogarithmicProjection.precomposeProjection hN' g hRightPole B,
    rfl, HEq.rfl, IsModification.comp L.toBase A.hom,
    rfl, HEq.rfl, IsModification.comp g B.hom⟩

end TauCeti.Toric.Fan
