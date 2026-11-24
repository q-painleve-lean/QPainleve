/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.Geometry.Toric.Fan.Boundary.NumberedPrime
public import QPainleve.Geometry.Toric.Fan.Boundary.Recovery
public import QPainleve.Geometry.Toric.Fan.Picard.StrictTransform

import QPainleve.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Recovering the Picard marking after an internal contraction

A toric identification of the base of a specified internal contraction recovers the
ordered toric blowup of its disjoint smooth centers. The comparison identifies the
strict boundary via the given boundary isomorphism and preserves the total exceptional
and strict ray classes. These are the classes used in reconstructing an isomorphism
from periods in the proof of [Gross, Hacking and Keel, Theorem 1.8][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public section

open AlgebraicGeometry CategoryTheory QPainleve.BlowupTower
open QPainleve (BlowupTower)
open TauCeti.AlgebraicGeometry LineBundleClass Scheme.IdealSheafData

namespace TauCeti.Toric.Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {Φ : Fan i} (b : Module.Basis (Fin 2) ℤ N)
  {X Y W : Scheme} {n : ℕ} {T : BlowupTower X n W}

local notation "S" => Spec (CommRingCat.of ℂ)
local notation "rankTwo" => Eq.trans (Module.finrank_eq_card_basis b) (Fintype.card_fin 2)
local notation "B[" h "]" => Φ.boundaryIdeal (IsComplete.nonempty_cones h)

private theorem toric_center_not_node (hc : Φ.IsComplete) {E : X.IdealSheafData}
    (t : X ⟶ S) [LocallyOfFinitePresentation (E.subschemeι ≫ t)]
    (a : X ≅ Φ.algebraicRealization) (ha : a.hom ≫ Φ.algebraicRealizationStructureMap = t)
    (h : (B[hc]).comap a.hom = E) [IsReduced E.subscheme] {q : E.subscheme}
    (hq : q ∈ (E.subschemeι ≫ t).smoothLocus) :
    ¬ (B[hc]).IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap
      (a.hom (E.subschemeι q)) := by
  have hnot : ¬ E.IsNodeOfReducedBoundary t (E.subschemeι q) := by
    rw [E.isNodeOfReducedBoundary_iff_of_isReduced]
    rintro ⟨z, hz, hn⟩
    exact (E.subschemeι ≫ t).not_isNodeAt_of_mem_smoothLocus
      (E.subschemeι.isClosedEmbedding.injective hz ▸ hq) hn
  have hnode := isNodeOfReducedBoundary_comap_iff_of_isOpenImmersion
    (B[hc]) Φ.algebraicRealizationStructureMap a.hom (E.subschemeι q)
  rw [ha, h] at hnode
  exact fun hn ↦ hnot (hnode.mpr hn)

/-- Recover the ordered internal model of a specified contraction to a toric pair.
The distinct projected centers lie in the smooth locus of the contracted boundary.
The returned isomorphisms identify the original surface and strict boundary over
the prescribed base identification, and pull back the labeled total exceptional
classes to the given ones. -/
theorem exists_ordered_toric_model_of_boundary_contraction
    (hΦ : Φ.IsRegular) (hc : Φ.IsComplete) {D : Y.IdealSheafData} {E : X.IdealSheafData}
    (t : X ⟶ S) [LocallyOfFinitePresentation (E.subschemeι ≫ t)]
    (hT : T.IsClosedPointTower X) (d : Y ≅ W) (a : X ≅ Φ.algebraicRealization)
    (ha : a.hom ≫ Φ.algebraicRealizationStructureMap = t)
    (hB : (B[hc]).comap a.hom = E)
    (v : D.subscheme ≅ E.subscheme) (hv : v.hom ≫ E.subschemeι = D.subschemeι ≫ d.hom ≫ T.toBase)
    (hinj : Function.Injective hT.baseCenter)
    (hcenters : ∀ j, ∃ q : E.subscheme, E.subschemeι q = hT.baseCenter j ∧
      q ∈ (E.subschemeι ≫ t).smoothLocus) :
    letI := hc.nonempty_cones
    ∃ (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ),
      let M := internalBlowupTower b s c
      ∃ (e : M.1 ≅ Y) (eB : (B[hc]).subscheme ≅ D.subscheme),
        IsLift a T M.2.toTower (d.symm ≪≫ e.symm) ∧
        e.hom ≫ d.hom ≫ T.toBase ≫ t = M.2.toTower.toBase ≫ Φ.algebraicRealizationStructureMap ∧
        eB.hom ≫ D.subschemeι = M.2.boundaryι ≫ e.hom ∧
        D.comap e.hom = M.2.boundaryι.ker ∧
        ∀ j, pullback e.hom (pullback d.hom (T.exceptionalClass j)) =
          M.2.toTower.exceptionalClass j := by
  let := hc.nonempty_cones
  obtain ⟨u, hu⟩ := (B[hc]).exists_iso_of_comap_eq_ker a E.subschemeι
    (hB.trans E.ker_subschemeι.symm)
  let : IsReduced (B[hc]).subscheme := by
    rw [boundaryIdeal_def]
    infer_instance
  let : IsReduced E.subscheme := isReduced_of_isOpenImmersion u.hom
  let eB := u.symm ≪≫ v.symm
  let f := eB.hom ≫ D.subschemeι ≫ d.hom
  have hf : f ≫ T.toBase ≫ a.hom = (B[hc]).subschemeι := by
    simp only [f, eB, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← reassoc_of% hv, Iso.inv_hom_id_assoc, ← hu, Iso.inv_hom_id_assoc]
  have hmem (j : Fin n) : a.hom (hT.baseCenter j) ∈ (B[hc]).support := by
    obtain ⟨q, hq, _⟩ := hcenters j
    rw [← SetLike.mem_coe, ← range_subschemeι]
    exact ⟨u.hom q, by simpa only [Scheme.Hom.comp_apply, hq] using
      (congrArg (fun g : E.subscheme ⟶ Φ.algebraicRealization ↦ g q) hu)⟩
  have hn (j : Fin n) : ¬ (B[hc]).IsNodeOfReducedBoundary Φ.algebraicRealizationStructureMap
      (a.hom (hT.baseCenter j)) := by
    obtain ⟨q, hq, hs⟩ := hcenters j
    rw [← hq]
    exact toric_center_not_node hc t a ha hB hs
  obtain ⟨z, ⟨-, ⟨g, ⟨hg, hgf⟩, -⟩⟩, -⟩ :=
    existsUnique_ordered_toric_model_of_disjoint_blowup_tower b hΦ hc hT a hinj hmem hn f hf
  let e := g.symm ≪≫ d.symm
  have hproj : e.hom ≫ d.hom = g.inv := by simp [e]
  have heB : eB.hom ≫ D.subschemeι =
      (internalBlowupTower b (Prod.fst ∘ z) (Prod.snd ∘ z)).2.boundaryι ≫ e.hom := by
    rw [← hgf]
    simp [e, f]
  refine ⟨Prod.fst ∘ z, Prod.snd ∘ z, e, eB, ?_, ?_, heB, ?_, fun j ↦ ?_⟩
  · have hh : d.symm ≪≫ e.symm = g := by
      apply Iso.ext
      simp [e]
    exact hh.symm ▸ hg
  · rw [← Category.assoc, hproj, ← ha, ← reassoc_of% hg.hom_toBase, Iso.inv_hom_id_assoc]
  · have hk :
        ((internalBlowupTower b (Prod.fst ∘ z) (Prod.snd ∘ z)).2.boundaryι ≫ e.hom).ker = D := by
      rw [← heB, Scheme.Hom.ker_comp_of_isIso, D.ker_subschemeι]
    rw [← hk, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  · rw [pullback_comp, hproj, ← hg.pullback_exceptionalClass j, pullback_comp,
      Iso.inv_hom_id, pullback_id]

section BoundaryClasses

variable [Nonempty Φ.cones] (hΦ : Φ.IsRegular)
  (s : Fin n → Φ.Ray) (c : Fin n → ℂˣ)

local notation "M" => internalBlowupTower b s c
local notation "J" => WithBoundary.toTower (Sigma.snd M)
local notation "hJ" => isClosedPointTower_internalBlowupTower b s c
local notation "ι" => WithBoundary.boundaryι (Sigma.snd M)
local notation "f" => Φ.algebraicRealization ↘ S

/-- A strict ray in an ordered toric model corresponds to an actual prime of
the identified boundary. Pullback along the model isomorphism identifies that
prime's Picard class with the strict ray class, in the same ray order. -/
theorem exists_boundaryPrimeEquiv_pullback_eq_strictRayBoundaryClass
    [IsLocallyNoetherian Y] [∀ y : Y, IsDomain (Y.presheaf.stalk y)]
    [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
    {D : Y.IdealSheafData} (e : M.1 ≅ Y) (he : D.comap e.hom = (ι).ker) :
    ∃ σ : Φ.Ray ≃ D.boundaryPrimes,
      (∀ ρ, (σ ρ).val = e.hom (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ).val) ∧
      ∀ ρ, Additive.ofMul (pullback e.hom (primeDivisorClass (D.boundaryPrimeEmbedding (σ ρ)))) =
        strictRayBoundaryClass hΦ rankTwo J hJ ρ := by
  classical
  let : IsIntegral M.1 := isIntegral_internalBlowupTower b s c hΦ
  let : IsNoetherian M.1 := (J).isNoetherian
  let : SmoothOfRelativeDimension 2 f :=
    rankTwo ▸ Φ.smoothOfRelativeDimension_algebraicRealizationStructureMap hΦ
  let : SmoothOfRelativeDimension 2 ((J).toBase ≫ f) := (hJ).smoothOfRelativeDimension f
  let := ((J).toBase ≫ f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let α := internalBlowupBoundaryPrimeEquiv hΦ b s c
  let t : (ι).ker.boundaryPrimes ≃ (D.comap e.hom).boundaryPrimes :=
    Set.equivOfEq (congrArg boundaryPrimes he.symm)
  let σ := α.trans (t.trans (D.boundaryPrimesEquivOfIso e))
  have hσ (ρ : Φ.Ray) : (σ ρ).val = e.hom (α ρ).val := by
    simp [σ, t]
  refine ⟨σ, hσ, fun ρ ↦ ?_⟩
  have hp : CodimensionOnePoint.mapOfIsOpenImmersion e.hom
      ((ι).ker.boundaryPrimeEmbedding (α ρ)) = D.boundaryPrimeEmbedding (σ ρ) := by
    apply Subtype.ext
    simpa only [CodimensionOnePoint.coe_mapOfIsOpenImmersion, coe_boundaryPrimeEmbedding]
      using (hσ ρ).symm
  rw [← hp, pullback_primeDivisorClass_mapOfIsOpenImmersion,
    ← picardHom_markedBoundaryMap_single_internalBlowupTower hΦ b s c ρ]
  have hα : (ι).ker.boundaryPrimeEmbedding (α ρ) =
      ⟨(α ρ).val, (mem_boundaryPrimes.mp (α ρ).property).2⟩ :=
    Subtype.ext (coe_boundaryPrimeEmbedding _ _)
  rw [hα]
  exact (picardHom_markedBoundaryMap_single_eq_primeDivisorClass hΦ b s c ρ).symm

local notation "Dtor" => Φ.boundaryIdeal inferInstance

/-- If the boundary identification sends the component of a ray to a numbered
component, the numbered Picard class pulls back to that ray's strict class.
The component matching uses the actual boundary isomorphism. -/
theorem pullback_numbered_boundaryPrime_eq_strictRayBoundaryClass
    [IsLocallyNoetherian Y] [∀ y : Y, IsDomain (Y.presheaf.stalk y)]
    [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
    {D : Y.IdealSheafData} [D.subscheme.Over S] [PrestableFamily (D.subscheme ↘ S)]
    [PrestableFamily ((Dtor).subscheme ↘ S)]
    {m l : ℕ} [NeZero m] [NeZero l] {γ δ : Type*}
    {p : γ → ((Dtor).subscheme ↘ S).smoothLocus} {q : δ → (D.subscheme ↘ S).smoothLocus}
    (C : Scheme.NodalCycleNumbering p m) (A : Scheme.NodalCycleNumbering q l)
    (hD : D.IsEffectiveCartier) (e : M.1 ≅ Y)
    (eB : (Dtor).subscheme ≅ D.subscheme) (heB : eB.hom ≫ D.subschemeι = (ι) ≫ e.hom)
    (ρ : Φ.Ray) (j : ZMod m) (j' : ZMod l)
    (hρ : C.component j = Φ.boundaryNormalizationComponentEquiv hΦ ρ)
    (hj : eB.hom (C.componentGenericPoint j) = A.componentGenericPoint j') :
    Additive.ofMul (pullback e.hom (primeDivisorClass (D.boundaryPrimeEmbedding
      (A.boundaryPrimeEquiv hD j')))) = strictRayBoundaryClass hΦ rankTwo J hJ ρ := by
  have he : D.comap e.hom = (ι).ker := by
    have hk : ((ι) ≫ e.hom).ker = D := by
      rw [← heB, Scheme.Hom.ker_comp_of_isIso, D.ker_subschemeι]
    rw [← hk, Scheme.Hom.comap_ker_comp_of_isClosedImmersion]
  obtain ⟨σ, hσ, hclass⟩ := exists_boundaryPrimeEquiv_pullback_eq_strictRayBoundaryClass
    b hΦ s c e he
  have hpoint : (internalBlowupBoundaryPrimeEquiv hΦ b s c ρ).val =
      (ι) (C.componentGenericPoint j) := by
    rw [internalBlowupBoundaryPrime_val, Scheme.NodalCycleNumbering.componentGenericPoint_def, hρ]
  have hPrime : σ ρ = A.boundaryPrimeEquiv hD j' := by
    apply Subtype.ext
    rw [hσ, hpoint, ← Scheme.Hom.comp_apply, ← heB, Scheme.Hom.comp_apply, hj,
      A.boundaryPrimeEquiv_apply_val]
  rw [← hPrime]
  exact hclass ρ

end BoundaryClasses

end TauCeti.Toric.Fan
