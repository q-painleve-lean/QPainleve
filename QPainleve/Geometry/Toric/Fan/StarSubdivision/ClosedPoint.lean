/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Canonical
public import QPainleve.Geometry.Toric.Fan.StarSubdivision.ProjectivePlane

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.Modules.Differentials.Restriction
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.ClosedPoints
import QPainleve.Geometry.Toric.BaseChange.FiniteType
import TauCeti.AlgebraicGeometry.Blowup.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.IdealSheaf.Reduced
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Hirzebruch models of point blowups of the plane

A projective linear change of coordinates moves a specified closed point
to the coordinate vertex of the plane fan. The star-subdivision comparison
then identifies the blowup with a Hirzebruch-one fan, including the projection
and the exceptional divisor. At a node of an anticanonical divisor the reduced
total boundary is again nodal and anticanonical. This gives the reduction of
the plane case to a ruled surface in [Gross, Hacking and Keel, Proposition 1.3][GHK].

[GHK]: https://arxiv.org/html/1106.4977v3#S1.Thmproposition3
-/

public section

open AlgebraicGeometry CategoryTheory Limits Module QPainleve QPainleve.BlowupTower
open Scheme.IdealSheafData
open TauCeti.AlgebraicGeometry LineBundleClass

namespace TauCeti.Toric.Fan

universe u

variable (k : Type u) [Field k] [IsAlgClosed k] {N V : Type u}
  [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (b : Basis (Fin 2) ℤ N) (hi : IsIntegralLattice i)

local notation "S" => Spec (CommRingCat.of k)
local notation "Π₀" => projectiveSpace b hi
local notation "X[" Φ "]" => Fan.finiteFanScheme k Φ
local notation "v₀" =>
  distinguishedSection (R := k) (projectiveSpace b hi) (projectiveSpaceMaximalCone b hi none)

private theorem exists_plane_iso_at_closed_point {X : Scheme} [X.Over S]
    (a : X[Π₀] ≅ X) [a.hom.IsOver S]
    (p : X) (hp : IsClosed ({p} : Set X)) :
    ∃ e : X[Π₀] ≅ X, e.hom.IsOver S ∧
      (X.fromSpecResidueField p).ker.comap e.hom = (v₀).ker := by
  let c := Pi.basisFun k (Fin 3)
  let t := projectivePlaneIso k b hi ≪≫ c.polynomialProjIso
  let e₀ := a.symm ≪≫ t
  let z := v₀ ≫ t.hom
  let o : S := IsLocalRing.closedPoint k
  have ht : t.hom.IsOver S := projectivePlaneIso_trans_polynomialProjIso_hom_isOver k b hi c
  have hz : z ≫ (_ ↘ S) = 𝟙 S := by
    simp only [z, Category.assoc, comp_over t.hom S, finiteFanScheme_over k,
      distinguishedSection_comp_finiteFanSchemeToSpec]
  have : IsClosedImmersion z := isClosedImmersion_of_comp_eq_id _ _ hz
  have hRange : Set.range z = {z o} :=
    Set.range_eq_singleton (fun x ↦ congrArg z (Subsingleton.elim x _))
  have hzclosed : IsClosed ({z o} : Set _) :=
    hRange ▸ z.isClosedEmbedding.isClosed_range
  have hp' : IsClosed ({e₀.hom p} : Set _) := by
    simpa only [Set.image_singleton] using e₀.hom.isClosedMap _ hp
  obtain ⟨d, hd⟩ := Proj.exists_symmetricAlgebraMapIso_hom_apply_eq_of_isClosed
    (z o) (e₀.hom p) hzclosed hp'
  let u := Proj.symmetricAlgebraMapIso k d
  let : u.hom.IsOver S := ⟨by
    rw [TauCeti.SymmetricAlgebra.over_eq_projToSpec, Proj.symmetricAlgebraMapIso_hom_projToSpec]⟩
  let e := t ≪≫ u ≪≫ e₀.symm
  have he : e.hom (v₀ o) = p := calc
    _ = e₀.inv (u.hom (z o)) := by
      rw [Scheme.Hom.comp_apply (v₀) t.hom]
      simp only [e, Iso.trans_hom, Iso.symm_hom, Scheme.Hom.comp_apply]
    _ = e₀.inv (e₀.hom p) := congrArg e₀.inv hd
    _ = p := by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
  let : e₀.inv.IsOver S := inferInstanceAs ((t.inv ≫ a.hom).IsOver S)
  refine ⟨e, inferInstanceAs ((t.hom ≫ u.hom ≫ e₀.inv).IsOver S), ?_⟩
  rw [← he, e.hom.comap_ker_fromSpecResidueField_apply, ← (v₀).ker_eq_ker_fromSpecResidueField]

/-- The blowup at a specified closed point of a projective plane over an algebraically
closed field admits a Hirzebruch-one toric model. In these coordinates the given blowup
projection is the star-subdivision morphism, and the exceptional ideal is the
boundary ideal of the negative section. -/
theorem exists_hirzebruch_one_model_of_plane_point_blowup {X : Scheme} [X.Over S]
    (a : X[Π₀] ≅ X) [a.hom.IsOver S]
    (p : X) (hp : IsClosed ({p} : Set X)) :
    let I := (X.fromSpecResidueField p).ker
    ∃ (Φ : Fan i) (hΦ : Φ.IsRegular) (_ : Φ.IsComplete) (d : Basis (Fin 2) ℤ N)
      (r : Φ.Ray) (J : Φ.IsSubdivision Π₀) (e : X[Π₀] ≅ X) (f : X[Φ] ≅ I.blowup),
      e.hom.IsOver S ∧ Set.range (Ray.primitiveGenerator (Phi := Φ)) =
        {d 0, d 1, -d 0, d 0 - d 1} ∧
      r.primitiveGenerator = d 0 ∧
      f.hom ≫ I.blowupToBase = J.toFanHom.finiteFanSchemeHom k ≫ e.hom ∧
      I.comap (f.hom ≫ I.blowupToBase) = Φ.rayDivisorIdeal k hΦ r := by
  intro I
  obtain ⟨e, he, hI⟩ := exists_plane_iso_at_closed_point k b hi a p hp
  let hPlane := isRegular_projectiveSpace b hi
  let σ := projectiveSpaceMaximalCone b hi none
  let Φ := Π₀.starSubdivisionAlong hPlane σ.property
  obtain ⟨hσ, d, g, hd, hr, hπ, hE, -⟩ :=
    exists_blowup_projectivePlane_vertex_hirzebruchOne k b hi none
  let J := Π₀.starSubdivisionAlong_isSubdivision hPlane σ.property hσ
  let r := Π₀.starSubdivisionAlongRay hPlane σ.property hσ
  have hCenter : I.comap e.hom = (v₀).ker := hI
  let f := g ≪≫ blowupIso e hCenter.symm
  have hf : f.hom ≫ I.blowupToBase = J.toFanHom.finiteFanSchemeHom k ≫ e.hom := by
    rw [Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase, ← Category.assoc, hπ]
  refine ⟨Φ, Π₀.isRegular_starSubdivisionAlong hPlane σ.property,
    J.isComplete_iff.mpr (isComplete_projectiveSpace b hi), d, r, J, e, f, he, hd, hr, hf, ?_⟩
  rw [hf, comap_comp, hCenter, ← hπ]
  exact hE

/-- Over an algebraically closed field, blowing up a node of an anticanonical boundary
on the plane gives a Hirzebruch-one surface with nodal anticanonical reduced total
boundary. This includes a node on a single irreducible component. The
exceptional divisor is the invariant negative section of the resulting model. -/
theorem exists_hirzebruch_one_model_of_plane_nodal_blowup {X : Scheme} [X.Over S]
    (a : X[Π₀] ≅ X) [a.hom.IsOver S] {D : X.IdealSheafData} (hD : D.IsEffectiveCartier)
    (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ X ↘ S))
    (p : X) (hp : IsClosed ({p} : Set X)) (hn : D.IsNodeOfReducedBoundary (X ↘ S) p) :
    let : SmoothOfRelativeDimension 2 (X ↘ S) := by
      let : Nonempty Π₀.cones := (isComplete_projectiveSpace b hi).nonempty_cones
      have := (smoothOfRelativeDimension_isStableUnderBaseChange 2).respectsIso
      rw [← MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 2) a.hom,
        comp_over a.hom S, finiteFanScheme_over k]
      have hRank : finrank ℤ N = 2 := (finrank_eq_card_basis b).trans (Fintype.card_fin 2)
      have hDim := Π₀.smoothOfRelativeDimension_finiteFanSchemeToSpec k
        (isRegular_projectiveSpace b hi)
      exact (congrArg (fun n ↦ SmoothOfRelativeDimension n
        ((projectiveSpace b hi).finiteFanSchemeToSpec k)) hRank).mp hDim
    LineBundleClass.mk hD.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle k X 2) →
    let I := (X.fromSpecResidueField p).ker
    ∃ (Φ : Fan i) (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) (d : Basis (Fin 2) ℤ N)
      (r : Φ.Ray) (f : X[Φ] ≅ I.blowup),
      let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
        let : Nonempty Φ.cones := hc.nonempty_cones
        rw [finiteFanScheme_over k]
        exact ((finrank_eq_card_basis d).trans (Fintype.card_fin 2)) ▸
          Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
      let π := f.hom ≫ I.blowupToBase
      let E := (D.comap π).radical
      Set.range (Ray.primitiveGenerator (Phi := Φ)) = {d 0, d 1, -d 0, d 0 - d 1} ∧
      r.primitiveGenerator = d 0 ∧ π.IsOver S ∧ I.comap π = Φ.rayDivisorIdeal k hΦ r ∧
      E ≤ Φ.rayDivisorIdeal k hΦ r ∧
      ∃ hE : E.IsEffectiveCartier,
        LineBundleClass.mk hE.toInvertibleSheaf = LineBundleClass.mk (canonicalBundle k X[Φ] 2) ∧
        AtWorstNodalOfRelativeDimensionOne (E.subschemeι ≫ X[Φ] ↘ S) := by
  intro hSmooth hDcan I
  let := hSmooth
  obtain ⟨Φ, hΦ, hc, d, r, J, e, f, he, hd, hr, hf, hI⟩ :=
    exists_hirzebruch_one_model_of_plane_point_blowup k b hi a p hp
  let : Nonempty Π₀.cones := (isComplete_projectiveSpace b hi).nonempty_cones
  let : IsIntegral X := IsIntegral.of_isIso a.hom
  let : X[Π₀].IsProjectiveOver k :=
    Scheme.IsProjectiveOver.of_isClosedImmersion k (finiteFanSchemeToProjectiveSpace k b hi)
  let : X.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k a.inv
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let T : BlowupTower X 1 I.blowup := .snoc .nil I
  have hT : IsNodalBoundaryTower D (X ↘ S) (𝟙 X) T :=
    .snoc .nil p hp rfl (by simpa only [toBase_nil, Category.id_comp, comap_id] using hn)
  have hπ : T.toBase = I.blowupToBase := by simp [T]
  let R := (D.comap T.toBase).radical
  obtain ⟨hR, hRN⟩ := hT.radical_comap_toBase hD hN
  let : I.blowup.Over S := ⟨T.toBase ≫ X ↘ S⟩
  let : SmoothOfRelativeDimension 2 (I.blowup ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (X ↘ S)
  have hRcan := (hT.canonicalClass_radical_comap_toBase_iff hD hN).mpr hDcan
  let : Nonempty Φ.cones := hc.nonempty_cones
  let : SmoothOfRelativeDimension 2 (X[Φ] ↘ S) := by
    rw [finiteFanScheme_over k]
    exact ((finrank_eq_card_basis d).trans (Fintype.card_fin 2)) ▸
      Φ.smoothOfRelativeDimension_finiteFanSchemeToSpec k hΦ
  let : e.hom.IsOver S := he
  have hfOver : f.hom ≫ T.toBase ≫ X ↘ S = X[Φ] ↘ S := by
    rw [← Category.assoc, hπ, hf, Category.assoc, comp_over e.hom S, comp_over]
  let : f.hom.IsOver S := ⟨hfOver⟩
  have hE : (D.comap (f.hom ≫ I.blowupToBase)).radical = R.comap f.hom := by
    rw [← hπ, comap_comp, radical_comap_of_isOpenImmersion]
  refine ⟨Φ, hΦ, hc, d, r, f, hd, hr, ⟨by rw [← hπ]; exact comp_over f.hom S⟩, hI, ?_, ?_⟩
  · have hcenter := (D.le_ker_fromSpecResidueField_iff_mem_support hp).mpr
      (mem_support_of_isNodeOfReducedBoundary hn)
    have hle : D.comap (f.hom ≫ I.blowupToBase) ≤ Φ.rayDivisorIdeal k hΦ r :=
      hI ▸ comap_mono (f.hom ≫ I.blowupToBase) hcenter
    have hred : IsReduced (Φ.rayDivisorIdeal k hΦ r).subscheme :=
      @isReduced_of_isIntegral _ (Φ.isIntegral_rayDivisor k hΦ r)
    simpa only [vanishingIdeal_support,
      (Φ.rayDivisorIdeal k hΦ r).isReduced_subscheme_iff_radical_eq.mp hred] using
      vanishingIdeal_antimono (support_antitone hle)
  rw [hE]
  refine ⟨hR.comap f.hom, ?_, ?_⟩
  · rw [← hR.pullback_mk_toInvertibleSheaf (hR.comap f.hom), hRcan, pullback_mk]
    exact mk_pullback_canonicalBundle k f.hom 2
  · let g := (R.comapIso f.hom).hom ≫ pullback.snd f.hom R.subschemeι
    have hNodal : AtWorstNodalOfRelativeDimensionOne (g ≫ R.subschemeι ≫ T.toBase ≫ X ↘ S) :=
      hRN.comp_of_etale g
    simpa only [g, Category.assoc, ← pullback.condition_assoc, comapIso_hom_fst_assoc, hfOver]
      using hNodal

end TauCeti.Toric.Fan
