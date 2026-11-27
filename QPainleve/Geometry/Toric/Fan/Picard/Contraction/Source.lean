/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.AffineSpace.Dimension
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.InternalCurve
public import QPainleve.Geometry.Toric.Fan.Boundary.Node
public import QPainleve.Geometry.Toric.Fan.Presentation.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.ExceptionalConfiguration
import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Recovery
import QPainleve.AlgebraicGeometry.Chow.NegativeCurve
import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange
import QPainleve.AlgebraicGeometry.IdealSheaf.ClosedImmersion
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.Geometry.Toric.Fan.Subdivision.Projective

/-!
# The ordered source contraction of a root-free toric presentation

The internal tower in a toric presentation contracts its auxiliary surface
to the toric base. For a root-free pair the projected centers are distinct,
and the contraction restricts to an isomorphism of the boundaries. This
supplies the source configuration in the proof of Theorem 1.8 of
[Gross, Hacking and Keel, *Moduli of surfaces with an anti-canonical cycle*][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry TauCeti.Toric Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} {b : Module.Basis (Fin 2) ℤ N}

local notation "SpecC" => Spec (CommRingCat.of k)
local notation "g(" X ")" => (X ↘ SpecC)
local notation "K(" X ")" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "rankTwo" => (Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2))
local notation "RootFree(" Y ", " B ")" =>
  (¬ ∃ (C : Scheme) (j : C ⟶ Y) (_ : IsClosedImmersion j) (_ : IsIntegral C)
    (hj : j.ker.IsEffectiveCartier), topologicalKrullDim C = 1 ∧
    Disjoint (Set.range j) (support B) ∧
    Chow.classIntersectionNumber k Y (LineBundleClass.mk hj.toInvertibleSheaf)⁻¹
      (LineBundleClass.mk hj.toInvertibleSheaf)⁻¹ = -2)

open Fan in
private theorem contraction_baseCenters_of_root_free (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
    {r : ℕ} (s : Fin r → Φ.Ray) (c : Fin r → kˣ)
    {Y : Scheme} [Y.Over (Spec (.of k))] (B : Y.IdealSheafData) (hroot : RootFree(Y, B)) :
    let : Nonempty Φ.cones := hc.nonempty_cones
    let D := Φ.toricBoundaryIdeal k hc.nonempty_cones
    let M := internalBlowupTower k b s c
    ∀ (a : Y ≅ M.1),
      a.hom ≫ M.2.toTower.toBase ≫ Φ.finiteFanSchemeToSpec k = g(Y) →
      (B.comap a.inv).support = M.2.boundaryι.ker.support →
      let H := isClosedPointTower_internalBlowupTower k b s c
      Function.Injective H.baseCenter ∧
        ∀ j, ∃ p : D.subscheme, D.subschemeι p = H.baseCenter j ∧
          ((D.subschemeι ≫ Φ.finiteFanSchemeToSpec k).stalkMap p).hom.FormallySmooth := by
  intro nΦ D M
  let := nΦ
  let : (Φ.finiteFanScheme k).IsProjectiveOver k :=
    Φ.isProjectiveOver_finiteFanScheme_of_isComplete k hΦ hc b
  let : SmoothOfRelativeDimension 2 g((Φ.finiteFanScheme k)) := by
    rw [Φ.finiteFanScheme_over k]
    exact ((Module.finrank_eq_card_basis b).trans (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  let J (j : Fin r) := (s j).internalCenter k b (c j)
  choose p hp hsm hpJ using fun j ↦ (s j).exists_closedPoint_formallySmooth_internalCenter k b (c j)
  have hJ (j : Fin r) : ∃ q : D.subscheme, IsClosed ({q} : Set D.subscheme) ∧
      (J j).val = (D.subscheme.fromSpecResidueField q).ker := ⟨p j, hp j, hpJ j⟩
  -- The ambient comparison and projected centers depend on the tower.
  dsimp only [M]
  suffices ∀ (U : Σ Z, WithBoundary D.subschemeι r Z),
      U = alongBoundary D.subschemeι J →
      ∀ (a : Y ≅ U.1),
        a.hom ≫ U.2.toTower.toBase ≫ Φ.finiteFanSchemeToSpec k = g(Y) →
        (B.comap a.inv).support = U.2.boundaryι.ker.support →
        ∀ H : IsClosedPointTower (Φ.finiteFanScheme k) U.2.toTower,
          Function.Injective H.baseCenter ∧
            ∀ j, ∃ q : D.subscheme, D.subschemeι q = H.baseCenter j ∧
              ((D.subschemeι ≫ Φ.finiteFanSchemeToSpec k).stalkMap q).hom.FormallySmooth
    from
    fun a ha hBa ↦ this _ (internalBlowupTower_eq_alongBoundary k b s c) a ha hBa _
  rintro _ rfl a ha hBa H
  obtain ⟨hdis, -, -⟩ := exceptional_configuration_alongBoundary_of_iso D.subschemeι J k B a
    (by rwa [Φ.finiteFanScheme_over k]) hBa hJ hroot
  refine ⟨?_, fun j ↦ ⟨p j, (H.baseCenter_alongBoundary p hpJ j).symm, hsm j⟩⟩
  intro j l h
  have he : p j = p l := D.subschemeι.injective
    ((H.baseCenter_alongBoundary p hpJ j).symm.trans (h.trans (H.baseCenter_alongBoundary p hpJ l)))
  by_contra hne
  have hd := hdis hne
  have hpJ' (k : Fin r) : (J k).val = (D.subscheme.fromSpecResidueField (p k)).ker := hpJ k
  dsimp only at hd
  rw [hpJ' j, hpJ' l, he] at hd
  let U := alongBoundary D.subschemeι J
  let x := a.inv (U.2.boundaryι (p l))
  have hx : U.2.toTower.toBase (a.hom x) = D.subschemeι (p l) := by
    simp only [x, ← Scheme.Hom.comp_apply, Category.assoc, Iso.inv_hom_id_assoc,
      WithBoundary.boundaryι_toBase]
  refine (Set.disjoint_left.mp hd) (a := x) ?_ ?_
  all_goals
    simp only [support_comap, TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
      support_map_of_isClosedImmersion]
    rw [hx]
    apply Set.mem_image_of_mem
    rw [Scheme.support_ker_fromSpecResidueField_of_isClosed (hp l)]
    exact Set.mem_singleton _

variable {X : Scheme} [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [hRat : Scheme.IsRationalOver (X ↘ Spec (.of k))]
  {D : X.IdealSheafData}

include hRat in
/-- A toric presentation of a root-free anticanonical pair supplies an ordered
contraction of its nodal auxiliary surface to the toric base. Its projected
centers are distinct smooth boundary points, and the contraction is an
isomorphism on the reduced boundary. -/
theorem exists_toric_contraction_of_root_free_presentation
    (h : D.HasToricPresentation g(X) b i)
    (hD : D.IsEffectiveCartier) (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K(X))
    (hroot : let : Smooth g(X) := SmoothOfRelativeDimension.smooth 2 _
      let : IsIntegral X := hRat.isIntegral_of_smooth
      ∀ p : CodimensionOnePoint X, (p : X) ∉ D.support →
        Chow.realIntersectionBilinForm k X (Chow.realPrimeDivisorClass k p)
          (Chow.realPrimeDivisorClass k p) ≠ -2) :
    ∃ (Φ : Fan i) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete)
      (r : ℕ) (s : Fin r → Φ.Ray) (c : Fin r → kˣ)
      (m : ℕ) (Y : Scheme) (T : BlowupTower X m Y),
      IsNodalBoundaryTower D g(X) (𝟙 X) T ∧
      let : Nonempty Φ.cones := hc.nonempty_cones
      let I := Φ.toricBoundaryIdeal k hc.nonempty_cones
      let E := (D.comap T.toBase).radical
      let M := Fan.internalBlowupTower k b s c
      let H := Fan.isClosedPointTower_internalBlowupTower k b s c
      let : LocallyOfFinitePresentation (I.subschemeι ≫ Φ.finiteFanSchemeToSpec k) :=
        (Φ.atWorstNodalOfRelativeDimensionOne_boundary k hΦ hc rankTwo).syntomic
          |>.locallyOfFinitePresentation
      ∃ a : Y ≅ M.1,
        a.hom ≫ M.2.toTower.toBase ≫ Φ.finiteFanSchemeToSpec k = T.toBase ≫ g(X) ∧
        E.comap a.inv = M.2.boundaryι.ker ∧ Function.Injective H.baseCenter ∧
        (∀ j, ∃ p : I.subscheme, I.subschemeι p = H.baseCenter j ∧
          p ∈ (I.subschemeι ≫ Φ.finiteFanSchemeToSpec k).smoothLocus) ∧
        ∃ v : E.subscheme ≅ I.subscheme,
          v.hom ≫ I.subschemeι = E.subschemeι ≫ a.hom ≫ M.2.toTower.toBase := by
  obtain ⟨r, ⟨Φ, hΦ, hc, s, c, m, Y, T, hT, e, he, hB⟩⟩ := (hasToricPresentation_iff ..).mp h
  let : Nonempty Φ.cones := hc.nonempty_cones
  let I := Φ.toricBoundaryIdeal k hc.nonempty_cones
  let E := (D.comap T.toBase).radical
  let M := Fan.internalBlowupTower k b s c
  let : Y.Over SpecC := ⟨T.toBase ≫ g(X)⟩
  let : Smooth g(X) := SmoothOfRelativeDimension.smooth 2 _
  let : IsIntegral X := hRat.isIntegral_of_smooth
  let : LocallyOfFinitePresentation (I.subschemeι ≫ Φ.finiteFanSchemeToSpec k) :=
    (Φ.atWorstNodalOfRelativeDimensionOne_boundary k hΦ hc rankTwo).syntomic
      |>.locallyOfFinitePresentation
  have hrootX : RootFree(X, D) := by
    rw [← Chow.exists_realPrimeDivisorClass_self_eq_neg_two_iff k hD hcan]
    rintro ⟨p, hp, hsq⟩
    exact hroot p hp hsq
  have hrootY : RootFree(Y, E) := by
    simpa only [E, support_radical] using (hT.exists_internal_minus_two_curve_iff k).not.mpr hrootX
  have ha : e.inv ≫ M.2.toTower.toBase ≫ Φ.finiteFanSchemeToSpec k = g(Y) := by
    rw [← he, Iso.inv_hom_id_assoc]
    rfl
  obtain ⟨hinj, hcenters⟩ := contraction_baseCenters_of_root_free (b := b) hΦ hc s c E hrootY
    e.symm ha (congrArg support hB)
  refine ⟨Φ, hΦ, hc, r, s, c, m, Y, T, hT, e.symm, ha, hB, hinj, ?_, ?_⟩
  · intro j
    obtain ⟨p, hp, hs⟩ := hcenters j
    exact ⟨p, hp, Scheme.Hom.mem_smoothLocus.mpr hs⟩
  · obtain ⟨v, hv⟩ := E.exists_iso_of_comap_eq_ker e M.2.boundaryι hB
    refine ⟨v.symm, (cancel_epi v.hom).mp ?_⟩
    rw [Iso.symm_hom, Iso.hom_inv_id_assoc, ← Category.assoc v.hom, hv,
      Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc, WithBoundary.boundaryι_toBase]

end AlgebraicGeometry.Scheme.IdealSheafData
