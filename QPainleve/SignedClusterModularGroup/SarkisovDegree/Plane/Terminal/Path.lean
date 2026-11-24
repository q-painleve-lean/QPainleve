/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Logarithmic.Factorization
public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Plane.Terminal.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Ramification
import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# The terminal resolved Sarkisov path between toric planes

A degree-one plane map gives a one-edge path between the specified logarithmic
projections on the resolving surface. This is the terminal case in the proof of
[Lutz's Theorem 8.4](https://arxiv.org/pdf/2005.05010v3#page=73).
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open TauCeti.Toric Fan.LogarithmicProjection Scheme.IdealSheafData

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "s" => (P ↘ S)
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "coords" => Pi.basisFun ℂ (Fin 3)
local notation "planeIso[" b "," h "]" =>
  (Fan.projectivePlaneIso b h ≪≫ Module.Basis.polynomialProjIso coords)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- A specified degree-one resolution between two toric plane presentations gives a
one-edge Sarkisov path on the original resolving surface. Its map is the fan equivalence
followed by the torus translation from
`existsUnique_toric_factorization_of_plane_degree_one`. Both given projections occur
as endpoints, with their common pole ideal. -/
theorem exists_sarkisov_path_of_plane_degree_one
    {Y : Scheme} {n : ℕ} {T : BlowupTower P n Y} (hT : IsClosedPointTower P T)
    (b b' : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (g : Y ⟶ P) (hg : g ≫ s = T.toBase ≫ s) (hbir : Scheme.BirationalOver g (𝟙 P))
    {D : Y.IdealSheafData} :
    let : IsNoetherian P := isNoetherian_of_finiteType s
    let : Y.Over S := ⟨T.toBase ≫ s⟩
    let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension s
    let : IsIntegral Y := hT.isIntegral s
    let x := (T.picardMarking hT s).symm (Additive.ofMul (pullback g H))
    (Module.Basis.picardTwistEquiv coords) x.1 = 1 →
    ∀ (A B : Fan.LogarithmicProjection i D),
      A.fan = Fan.projectiveSpace b hi →
      B.fan = Fan.projectiveSpace b' hi →
      A.hom ≍ T.toBase ≫ (planeIso[b,hi]).inv →
      B.hom ≍ g ≫ (planeIso[b',hi]).inv →
      ∃ (e : FanEquiv A.fan B.fan) (c : Multiplicative (N →+ ℤ) →* ℂˣ)
        (p : SarkisovPath A B),
        @Quiver.Path.length _ sarkisovQuiver A B p = 1 ∧
        p.rationalMap =
          (e.toFanHom.algebraicMap ≫ (B.fan.torusTranslation c).hom).toRationalMap := by
  intro hNoeth hY hSmooth hInt x hd A B hA hB ha hb
  let := hNoeth
  let := hY
  let := hSmooth
  let := hInt
  let : g.IsOver S := ⟨hg⟩
  rcases A with ⟨Φ, hΦ, hcΦ, a, haOver, haDom, haPole⟩
  rcases B with ⟨Ψ, hΨ, hcΨ, q, hqOver, hqDom, hqPole⟩
  dsimp only at hA hB ha hb
  subst Φ Ψ
  obtain rfl : a = T.toBase ≫ (planeIso[b,hi]).inv := eq_of_heq ha
  obtain rfl : q = g ≫ (planeIso[b',hi]).inv := eq_of_heq hb
  have hdim (d : Basis (Fin 2) ℤ N) :
      SmoothOfRelativeDimension 2 ((Fan.projectiveSpace d hi).algebraicRealization ↘ S) := by
    let := (Fan.isComplete_projectiveSpace d hi).nonempty_cones
    have hRank := (finrank_eq_card_basis d).trans (Fintype.card_fin 2)
    simpa only [hRank, Fan.algebraicRealization_over] using
      (Fan.projectiveSpace d hi).smoothOfRelativeDimension_algebraicRealizationStructureMap
        (Fan.isRegular_projectiveSpace d hi)
  let := hdim b
  let := hdim b'
  let : T.toBase.IsOver S := ⟨rfl⟩
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver b hi coords
  let := Fan.projectivePlaneIso_trans_polynomialProjIso_hom_isOver b' hi coords
  have ha' := haPole
  have hb' := hqPole
  simp only [comap_comp, ramificationIdealSheaf_comp ℂ T.toBase (planeIso[b,hi]).inv 2,
    ramificationIdealSheaf_eq_top_of_isOpenImmersion, comap_top, mul_top,
    ← hT.ramificationIdealSheafToBase_def ℂ] at ha'
  simp only [comap_comp, ramificationIdealSheaf_comp ℂ g (planeIso[b',hi]).inv 2,
    ramificationIdealSheaf_eq_top_of_isOpenImmersion, comap_top, mul_top] at hb'
  obtain ⟨⟨e, c⟩, hcomm, -⟩ :=
    hT.existsUnique_toric_factorization_of_plane_degree_one b hi b' hi g hg hbir D hd ha' hb'
  let A : Fan.LogarithmicProjection i D :=
    ⟨_, hΦ, hcΦ, _, haOver, haDom, haPole⟩
  let B : Fan.LogarithmicProjection i D :=
    ⟨_, hΨ, hcΨ, _, hqOver, hqDom, hqPole⟩
  let : Nonempty A.fan.cones := hcΦ.nonempty_cones
  let : Nonempty B.fan.cones := hcΨ.nonempty_cones
  let f := e.toFanHom.algebraicMap ≫ (B.fan.torusTranslation c).hom
  have hEq : A.hom ≫ f = B.hom := by
    apply (cancel_mono (planeIso[b',hi]).hom).mp
    simpa only [A, B, f, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hcomm
  let edge : SarkisovStep A B :=
    ⟨f.toRationalMap, .toricIso e c, by
      rw [Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom, hEq]⟩
  let path : SarkisovPath A B := @Quiver.Hom.toPath _ sarkisovQuiver A B edge
  exact ⟨e, c, path, @Quiver.Path.length_toPath _ sarkisovQuiver A B edge,
    (path.rationalMap_eq_iff _).mpr edge.comp_rationalMap⟩

end QPainleve.BlowupTower.IsClosedPointTower
