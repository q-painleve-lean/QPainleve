/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Centres
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Homaloidal
import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Blowup.Tower.Multiplicity
import QPainleve.AlgebraicGeometry.LineBundle.Ample
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.Sections.Domain
import QPainleve.AlgebraicGeometry.RationalMap.ClosedImmersion
import QPainleve.AlgebraicGeometry.RationalMap.Modification

/-!
# Moving base ideals of plane resolutions

A specified point-blowup resolution of a rational map to the plane determines the
multiplicities of its moving line system in the ordered Picard marking. The first
center over a proper base point has order at least that of any center over the same
point. This gives the proper high-multiplicity center in the plane case of Lutz's
factorization argument in [the appendix to Hacking and Keating][HKL], Definition 8.5
and Proposition 8.11.

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=69
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry LineBundleClass TauCeti.SymmetricAlgebra
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor

universe u

namespace QPainleve.BlowupTower.IsClosedPointTower

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {n : ℕ}
  {T : BlowupTower X n Y} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)

private theorem exists_moving_plane_presentation (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let : IsIntegral Y := hT.isIntegral f
    let : Surjective T.toBase := hT.surjective f
    let b : Module.Basis (ULift.{u} (Fin 3)) k (Fin 3 → k) :=
      (Pi.basisFun k (Fin 3)).reindex Equiv.ulift.symm
    ∃ (L : InvertibleSheaf X) (s : Fin 3 → Γ(L.obj, ⊤)) (i : Fin 3)
      (hi : Dense (L.obj.nonvanishingLocus (s i) : Set X)),
      (g ≫ b.polynomialProjIso.inv).toRationalMap = T.toBase.toRationalMap.comp
        (L.obj.partialMapToProjectiveSpace f (s ∘ ULift.down) (ULift.up i) hi).toRationalMap ∧
      ∀ p : CodimensionOnePoint X, (p : X) ∉ (⨆ j, L.zeroIdeal (s j)).support := by
  intro hNoeth hIntegral hSurj b
  let := hNoeth
  let := hIntegral
  let := hSurj
  have := (f).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have : IsModification T.toBase := hT.isModification_of_smoothOfRelativeDimension_two f
  let h := g ≫ b.polynomialProjIso.inv
  let π := Proj.toSpecCoeff (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin 3)) k)
  have hover : h ≫ π = T.toBase ≫ f := by
    dsimp only [h, π]
    rw [Category.assoc, ← b.polynomialProjIso_hom_over, Iso.inv_hom_id_assoc]
    exact hg
  obtain ⟨q, hq, -⟩ := T.toBase.existsUnique_rationalMap_comp_eq_of_isModification h.toRationalMap
  have : q.IsOver f π := by
    apply Scheme.RationalMap.isOver_iff.mpr
    apply Scheme.RationalMap.comp_left_injective T.toBase.toRationalMap
    dsimp only
    rw [Scheme.RationalMap.comp_compHom, hq, Scheme.Hom.toRationalMap_compHom, hover,
      Scheme.RationalMap.comp_toRationalMap, Scheme.Hom.toRationalMap_compHom]
  obtain ⟨A, hA⟩ := X.exists_isAmple_of_isProjectiveOver k
  obtain ⟨L, s, i, hi, hs⟩ := q.exists_projective_section_presentation f hA
  obtain ⟨M, t, hd, ht, hbase⟩ := L.exists_moving_projective_presentation f s hi
  refine ⟨M, t ∘ ULift.up, i.down, hd, ?_, ?_⟩
  · have hreindex : ((ULift.up : Fin 3 → ULift.{u} (Fin 3)) ∘ ULift.down) = id :=
      funext ULift.up_down
    simpa only [Function.comp_assoc, hreindex, Function.comp_id, ht, hs] using hq.symm
  · have hsum : (⨆ j : Fin 3, M.zeroIdeal (t (ULift.up j))) = ⨆ j, M.zeroIdeal (t j) := by
      rw [iSup_ulift]
    simp only [Function.comp_apply, hsum, hbase]
    exact notMem_support_baseIdeal_movingPart _ _

/-- The moving base ideal of the specified plane map is principalized by the given
tower, and its support is the indeterminacy locus of that map. Its successive
base orders are the negatives of the exceptional coordinates of the pulled-back
hyperplane class. Extra blowups are allowed. -/
theorem exists_moving_base_ideal_of_plane_resolution (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let : IsIntegral Y := hT.isIntegral f
    let : Surjective T.toBase := hT.surjective f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    ∃ (q : X ⤏ P) (J : X.IdealSheafData), T.toBase.toRationalMap.comp q = g.toRationalMap ∧
      (q.domain : Set X) = (J.support : Set X)ᶜ ∧ J ≠ ⊥ ∧
      (∀ p : CodimensionOnePoint X, (p : X) ∉ J.support) ∧
      (J.comap T.toBase).IsEffectiveCartier ∧
      ∀ j, -v.2 j = (hT.baseMultiplicities J j : ℤ) := by
  intro hNoeth hIntegral hSurj v
  let := hNoeth
  let := hIntegral
  let := hSurj
  obtain ⟨L, s, i, hi, hrep, hmove⟩ := hT.exists_moving_plane_presentation g hg
  obtain ⟨hI, hv⟩ :=
    hT.picardMarking_symm_pullback_hyperplane_of_baseIdeal L s i hi g hg hrep hmove
  let J := ⨆ j, L.zeroIdeal (s j)
  have hJ : J ≠ ⊥ := by
    intro h
    apply hI.genericPoint_notMem_support
    have h' : (⨆ j, L.zeroIdeal (s j)) = ⊥ := h
    rw [h', Scheme.IdealSheafData.comap_bot, Scheme.IdealSheafData.support_bot]
    exact Set.mem_univ _
  let b : Module.Basis (ULift.{u} (Fin 3)) k (Fin 3 → k) :=
    (Pi.basisFun k (Fin 3)).reindex Equiv.ulift.symm
  let φ := (L.obj.partialMapToProjectiveSpace f (s ∘ ULift.down) (ULift.up i) hi).toRationalMap
  refine ⟨φ.compHom b.polynomialProjIso.hom, J, ?_, ?_, hJ, hmove, hI, fun j ↦ ?_⟩
  · have hφ : T.toBase.toRationalMap.comp φ = (g ≫ b.polynomialProjIso.inv).toRationalMap :=
      hrep.symm
    rw [Scheme.RationalMap.comp_compHom, hφ, Scheme.Hom.toRationalMap_compHom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · have hbase : (⨆ j : ULift.{u} (Fin 3), L.zeroIdeal ((s ∘ ULift.down) j)) = J :=
      iSup_ulift _
    ext x
    rw [Scheme.RationalMap.domain_compHom_of_isClosedImmersion]
    exact (L.mem_domain_partialMapToProjectiveSpace_iff_notMem_support f (s ∘ ULift.down) hi
      (by rwa [hbase]) x).trans (by rw [hbase]; rfl)
  · rw [congrArg Prod.snd hv]
    exact neg_neg _

/-- The first center over the image of a chosen center of a plane resolution
has at least its order in the pulled-back hyperplane marking. -/
theorem exists_first_baseCenter_ge_of_plane_resolution (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f) (j : Fin n) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    ∃ i : Fin n, hT.baseCenter i = hT.baseCenter j ∧
      (∀ l < i, hT.baseCenter l ≠ hT.baseCenter i) ∧ -v.2 j ≤ -v.2 i := by
  intro hNoeth v
  let := hNoeth
  obtain ⟨_, J, -, -, hJ, -, -, hv⟩ := hT.exists_moving_base_ideal_of_plane_resolution g hg
  let A : Set (Fin n) := {i | hT.baseCenter i = hT.baseCenter j}
  obtain ⟨i, hi, hmin⟩ := (wellFounded_lt (α := Fin n)).has_min A ⟨j, rfl⟩
  have hfirst (l : Fin n) (hl : l < i) : hT.baseCenter l ≠ hT.baseCenter i :=
    fun h ↦ hmin l (h.trans hi) hl
  refine ⟨i, hi, hfirst, ?_⟩
  rw [hv j, hv i]
  exact Int.ofNat_le.mpr (hT.baseMultiplicities_le_of_first_baseCenter f J hJ hi hfirst)

end QPainleve.BlowupTower.IsClosedPointTower
