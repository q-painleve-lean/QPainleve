/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.SarkisovDegree.Induction.Step

import QPainleve.AlgebraicGeometry.Modules.Differentials.PoleIdeal
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Preparation
import QPainleve.SignedClusterModularGroup.SarkisovDegree.Quadric.PreparedSections
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# Marked quadric preparation

The toric preparation of a Hirzebruch surface resolves all its links on a
single nodal blowup tower. The prepared quadric carries the same map to the
target plane, the same ruling degree, and a specified high first order on
the retained fiber. Bounds on the orders over the open sections also persist.

This is the preparation used in [Lutz, Proposition 8.11, Case C][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=73
-/

public section

open AlgebraicGeometry CategoryTheory Module QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra Scheme.IdealSheafData

namespace TauCeti.Toric.Fan.LogarithmicProjection

open scoped Sarkisov

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "P" => Proj (homogeneousSubmodule ℂ (Fin 3 → ℂ))
local notation "s" => (P ↘ S)
local notation "H" => LineBundleClass.mk (Proj.symmetricAlgebraTwistingBundle ℂ (Fin 3 → ℂ) 1)
local notation "planeIso[" b "," hi "]" =>
  (Fan.projectivePlaneIso b hi ≪≫ Basis.polynomialProjIso (Pi.basisFun ℂ (Fin 3)))
local notation "mark[" T "," hT "," f "," g "]" =>
  LinearEquiv.symm (BlowupTower.picardMarking T hT f) (Additive.ofMul (pullback g H))
local notation "obj[" F "," A "]" => @Prefunctor.obj _ sarkisovQuiver _ sarkisovQuiver F A
local notation "mapPath[" F "," p "]" =>
  @Prefunctor.mapPath _ sarkisovQuiver _ sarkisovQuiver F _ _ p
local notation "total[" D "," T "]" =>
  Scheme.IdealSheafData.radical (Scheme.IdealSheafData.comap D (BlowupTower.toBase T))
local notation "over[" U "]" => OverClass.ofHom ((BlowupTower.toBase U) ≫ _ ↘ S)
local notation "smooth[" h "]" =>
  IsClosedPointTower.smoothOfRelativeDimension (IsPointTowerWith.isClosedPointTower h) (_ ↘ S)
local notation "integral[" h "]" =>
  IsClosedPointTower.isIntegral (IsPointTowerWith.isClosedPointTower h) (_ ↘ S)

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {X : Scheme} [X.Over S] [SmoothOfRelativeDimension 2 (X ↘ S)]
  [IsIntegral X] [IsNoetherian X] {D : X.IdealSheafData}
  (A B : LogarithmicProjection i D)
  (b : Basis (Fin 2) ℤ N) (a : ℕ) (r : Fin 4 ≃ A.fan.Ray)
  (hr : (fun j ↦ (r j).primitiveGenerator) = ![b 0, b 1, -b 0, (a : ℤ) • b 0 - b 1])
  {Y : Scheme} {n : ℕ} {T : BlowupTower A.fan.algebraicRealization n Y}
  (hT : IsClosedPointTower A.fan.algebraicRealization T) (k : X ≅ Y) (g : Y ⟶ P)

local notation "rankTwo" => Eq.trans (finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "f[" Δ "]" => (Fan.algebraicRealization Δ ↘ S)
local notation "fA" => f[A.fan]
local notation "sourceSmooth" =>
  Eq.mp (congrArg (fun d ↦ SmoothOfRelativeDimension d fA) rankTwo)
    (A.fan.smoothOfRelativeDimension_algebraicRealizationStructureMap A.isRegular)
local notation "center[" ρ "," c "]" =>
  Fan.Ray.binomialCenter ρ rankTwo (Basis.detDualEquiv_self b (Fan.Ray.primitiveGenerator ρ))
    (Fan.Ray.surjective_detCharacter ρ b) c (IsLocalRing.closedPoint ℂ)
local notation "sectionRay[" t "]" => (![0, 2] : Fin 2 → Fin 4) t

/-- Prepare a specified marked Hirzebruch-to-plane resolution for the quadric
decrease. The resolved path starts at the pullback of the given first
projection. The prepared tower resolves the pullback of the given plane
target, and its high center on the retained fiber is still first over its
point. The ruling degree is unchanged. If the orders over the open sections
start at most half that degree, the prepared section orders have the same bound. -/
theorem exists_marked_quadric_preparation_of_hirzebruch
    (hg : g ≫ s = T.toBase ≫ fA) (hbir : Scheme.BirationalOver g (𝟙 P))
    (j : Fin n) (c : ℂˣ) (hj : hT.baseCenter j = center[r 1,c])
    (hfirst : ∀ k < j, hT.baseCenter k ≠ hT.baseCenter j)
    (b' : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)
    (hD : D.IsEffectiveCartier)
    (hNode : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (hhA : A.hom = k.hom ≫ T.toBase)
    (hB : B.fan = Fan.projectiveSpace b' hi)
    (hhB : B.hom ≍ k.hom ≫ g ≫ (planeIso[b',hi]).inv) :
    let : Nonempty A.fan.cones := A.isComplete.nonempty_cones
    let : SmoothOfRelativeDimension 2 fA := sourceSmooth
    let : Smooth fA := SmoothOfRelativeDimension.smooth 2 _
    let : IsNoetherian A.fan.algebraicRealization := isNoetherian_of_finiteType fA
    let x := mark[T,hT,fA,g]
    let β := (A.fan.hirzebruchPicardBasis b a A.isRegular r hr).repr x.1 1
    β < 2 * (-x.2 j) →
    ∃ (m : ℕ) (W : Scheme) (R : BlowupTower X m W)
      (hR : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) R),
      let : W.Over S := over[R]
      let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hR]
      let : IsIntegral W := integral[hR]
      let F := precomposeSarkisovOfNodalTower rankTwo hD hNode hR
      ∃ (C : LogarithmicProjection i total[D,R]) (p : SarkisovPath (obj[F,A]) C)
        (Ψ : Fan i) (hΨ : Ψ.IsRegular) (hcΨ : Ψ.IsComplete)
        (u : Fin 4 ≃ Ψ.Ray)
        (hu : (fun l ↦ (u l).primitiveGenerator) = ![b 0, b 1, -b 0, (0 : ℤ) • b 0 - b 1])
        (l : ℕ) (Z : Scheme) (U : BlowupTower Ψ.algebraicRealization l Z)
        (hU : IsClosedPointTower Ψ.algebraicRealization U) (e : W ≅ Z) (j' : Fin l) (g' : Z ⟶ P),
      C.fan = Ψ ∧ C.hom ≍ e.hom ≫ U.toBase ∧ @Quiver.Path.length _ sarkisovQuiver _ _ p = 2 * a ∧
      g' ≫ s = U.toBase ≫ f[Ψ] ∧ Scheme.BirationalOver g' (𝟙 P) ∧
      (obj[F,B]).hom ≍ e.hom ≫ g' ≫ (planeIso[b',hi]).inv ∧
      let : Nonempty Ψ.cones := hcΨ.nonempty_cones
      let : SmoothOfRelativeDimension 2 f[Ψ] :=
        rankTwo ▸ Ψ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΨ
      let y := mark[U,hU,f[Ψ],g']
      let β' := (Ψ.hirzebruchPicardBasis b 0 hΨ u hu).repr y.1 1
      hU.baseCenter j' = center[u 1,c] ∧
      (∀ l < j', hU.baseCenter l ≠ hU.baseCenter j') ∧
      β' = β ∧ -y.2 j' = -x.2 j ∧ β' < 2 * (-y.2 j') ∧
      ((∀ (t : Fin 2) (z : ℂˣ) (l : Fin n), hT.baseCenter l = center[r sectionRay[t],z] →
          (∀ k < l, hT.baseCenter k ≠ hT.baseCenter l) → 2 * (-x.2 l) ≤ β) →
        ∀ (t : Fin 2) (z : ℂˣ) (j : Fin l),
          hU.baseCenter j = center[u sectionRay[t],z] → 2 * (-y.2 j) ≤ β') := by
  intro hcones hSmooth hSmoothBase hNoeth x β hhigh
  let := hcones
  let := hSmooth
  let := hSmoothBase
  let := hNoeth
  let : A.fan.algebraicRealization.IsProjectiveOver ℂ :=
    A.fan.isProjectiveOver_algebraicRealization_of_isComplete A.isRegular A.isComplete b
  let : Y.Over S := over[T]
  let : SmoothOfRelativeDimension 2 (Y ↘ S) := hT.smoothOfRelativeDimension fA
  let : IsIntegral Y := hT.isIntegral fA
  let : IsNoetherian Y := T.isNoetherian
  let : k.hom.IsOver S := ⟨(Category.assoc k.hom T.toBase fA).symm.trans
    (hhA ▸ comp_over A.hom S)⟩
  let : k.inv.IsOver S := inferInstance
  let E := D.comap k.inv
  let : Smooth (Y ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : T.toBase.IsOver S := ⟨rfl⟩
  have hpole : (A.fan.boundaryIdeal A.isComplete.nonempty_cones).comap T.toBase =
      E * ramificationIdealSheaf ℂ T.toBase := by
    have h := comap_eq_mul_ramificationIdealSheaf_comp_iff_of_isIso ℂ k.hom T.toBase 2
      (D := A.fan.boundaryIdeal A.isComplete.nonempty_cones) (Q := D)
    rw [IsIso.inv_eq_of_hom_inv_id k.hom_inv_id] at h
    apply h.mp
    exact (congrArg (A.fan.boundaryIdeal A.isComplete.nonempty_cones).comap hhA).symm.trans
      (A.comap_boundaryIdeal.trans (congrArg (D * ·) (ramificationIdealSheaf_congr ℂ hhA)))
  -- Prepare the quadric in the source tower coordinates and transport the plane map.
  obtain ⟨Q, m, W, R, hR, q, hW, _, _, u, hu, hProj, l, Z, U, hU, e, j', hq, hq',
    heOver, _, hpath, _, hj', hfirst', _, hβ, hm, hh, _⟩ :=
    hT.exists_prepared_quadric_resolution_of_high_fiber_center b a A.isRegular A.isComplete r hr
      j c hj (hj ▸ hfirst) (pullback g H) E (hD.comap_of_isDominant k.inv) hpole hhigh
  let : W.Over S := over[R]
  let : SmoothOfRelativeDimension 2 (W ↘ S) := smooth[hR]
  let : IsIntegral W := hW
  obtain ⟨L, C, p, hL, hhL, hC, hhC, hlen, _⟩ := hpath
  let g' := e.inv ≫ R.toBase ≫ g
  have hg' : g' ≫ s = U.toBase ≫ f[Q.model 0] := by
    calc
      g' ≫ s = e.inv ≫ (R.toBase ≫ Y ↘ S) := by
        simp only [g', Category.assoc, hg]
        rfl
      _ = U.toBase ≫ f[Q.model 0] := by rw [← heOver, Iso.inv_hom_id_assoc]
  let : IsModification R.toBase :=
    hR.isClosedPointTower.isModification_of_smoothOfRelativeDimension_two (Y ↘ S)
  obtain ⟨v, hv⟩ := IsModification.birationalOver (e.inv ≫ R.toBase)
  have hbirToSource : Scheme.BirationalOver g' g :=
    ⟨v, by simpa only [g', Category.assoc, Category.comp_id] using congrArg (· ≫ g) hv⟩
  let := hProj
  have hlow := hT.base_order_le_half_on_prepared_quadric_sections b a A.isRegular A.isComplete
    (Q.model_regular 0) (Q.model_complete 0) r u hr hu hR.isClosedPointTower hU e
    Q.common_source (Q.common_model 0) q hq hq' g hg
  -- Descend the refinement from the coordinates of the source point tower.
  let hnil : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) (.nil : BlowupTower X 0 X) := .nil
  have hsupp : (E.comap k.hom).support =
      (D.comap (.nil : BlowupTower X 0 X).toBase).support := by
    simp [E, ← comap_comp]
  have hk : k.hom ≫ Y ↘ S = (.nil : BlowupTower X 0 X).toBase ≫ X ↘ S := by
    simpa only [toBase_nil, Category.id_comp] using comp_over k.hom S
  obtain ⟨V, J, d, hJ, hbase, hideal⟩ := hnil.exists_append_of_iso hR k hk hsupp
  simp only [toBase_nil, Category.comp_id] at hbase
  let : V.Over S := over[J]
  let : SmoothOfRelativeDimension 2 (V ↘ S) := smooth[hJ]
  let : IsIntegral V := integral[hJ]
  have hd : d.hom ≫ (R.toBase ≫ Y ↘ S) = J.toBase ≫ X ↘ S := by
    rw [hbase]
    simp only [Category.assoc, comp_over k.inv S]
  let : d.hom.IsOver S := ⟨hd⟩
  let F := precomposeSarkisovOfNodalTower (i := i) rankTwo hD hNode hJ
  let K := precomposeSarkisovOfIso (i := i) rankTwo d hideal.symm
  -- Recover the specified source and target on the lifted resolving surface.
  have hStart : obj[K,L] = obj[F,A] := by
    have hK := precomposeSarkisovOfIso_obj_fan rankTwo d hideal.symm L
    have hF := precomposeSarkisovOfNodalTower_obj_fan rankTwo hD hNode hJ A
    refine LogarithmicProjection.ext ((hK.trans hL).trans hF.symm) ?_
    have h := (precomposeSarkisovOfIso_obj_hom rankTwo d hideal.symm L).trans
      (heq_comp rfl rfl (congrArg Fan.algebraicRealization hL) HEq.rfl hhL)
    refine h.trans ?_
    simpa only [hbase, hhA, Category.assoc, Iso.inv_hom_id_assoc] using
      (precomposeSarkisovOfNodalTower_obj_hom rankTwo hD hNode hJ A).symm
  have hTarget : (obj[F,B]).hom ≍ (d ≪≫ e).hom ≫ g' ≫ (planeIso[b',hi]).inv := by
    have h := (precomposeSarkisovOfNodalTower_obj_hom rankTwo hD hNode hJ B).trans
      (heq_comp rfl rfl (congrArg Fan.algebraicRealization hB) HEq.rfl hhB)
    simpa only [hbase, g', Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc] using h
  have hEnd := (precomposeSarkisovOfIso_obj_hom rankTwo d hideal.symm C).trans
    (heq_comp rfl rfl (congrArg Fan.algebraicRealization hC) HEq.rfl hhC)
  refine ⟨0 + m, V, J, hJ, obj[K,C], hStart ▸ mapPath[K,p], Q.model 0, Q.model_regular 0,
    Q.model_complete 0, u, hu, l, Z, U, hU, d ≪≫ e, j', g',
    (precomposeSarkisovOfIso_obj_fan ..).trans hC,
    by simpa only [Iso.trans_hom, Category.assoc] using hEnd, ?_, hg', hbirToSource.trans hbir,
    hTarget, hj', fun l hl ↦ hj'.symm ▸ hfirst' l hl, ?_, ?_, ?_, ?_⟩
  · generalize obj[F,A] = L' at hStart ⊢
    cases hStart
    simpa only [Prefunctor.length_mapPath] using hlen
  · simpa only [g', Category.assoc, pullback_comp] using hβ
  · simpa only [g', Category.assoc, pullback_comp] using hm
  · simpa only [g', Category.assoc, pullback_comp] using hh
  · exact fun h t z ↦ hlow t z (h t z)

end TauCeti.Toric.Fan.LogarithmicProjection
