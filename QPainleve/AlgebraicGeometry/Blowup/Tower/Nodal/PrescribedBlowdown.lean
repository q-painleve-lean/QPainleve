/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Numbering
public import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Basic
public import QPainleve.AlgebraicGeometry.Chow.NodalIntersection
public import QPainleve.AlgebraicGeometry.Chow.RationalSurface.Basic
public import QPainleve.AlgebraicGeometry.Modules.Differentials.Canonical
public import TauCeti.AlgebraicGeometry.IntersectionNumber.ExceptionalCurve.Basic

import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.Blowdown
import QPainleve.AlgebraicGeometry.Blowup.Tower.StrictTransform.PointBlowdown
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Chow.RationalSurface.ExceptionalCurve
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField

/-!
# Nodal blowdown of a numbered boundary component

A component of square `-1` in a numbered anticanonical cycle with at least two
components can be blown down at the specified label. Its two incident branches
give the two units of intersection with the other components, including when
both branches meet the same component. This computes its canonical degree for
the exceptional-curve test. The surviving components descend by the
orthogonal projection formula for point blowdowns.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace QPainleve QPainleve.BlowupTower
open TauCeti.AlgebraicGeometry Scheme.IdealSheafData LineBundleClass

universe u v

namespace AlgebraicGeometry.Scheme.NodalCycleNumbering

variable {k : Type u} [Field k] [IsAlgClosed k]

local notation "S(" k ")" => Spec (CommRingCat.of k)
local notation "K[" k "," X "]" => LineBundleClass.mk (canonicalBundle k X 2)
local notation "g[" k "," X "]" => (X ↘ S(k))
local notation "J[" p "]" => vanishingIdeal (Closeds.mk (closure {p}) isClosed_closure)

variable {X : Scheme.{u}} [X.Over S(k)] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 g[k,X]]
  {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ S(k))]
  {ι : Type v} {marks : ι → (D.subscheme ↘ S(k)).smoothLocus}
  {n : ℕ} [NeZero n] (A : NodalCycleNumbering marks n) (hD : D.IsEffectiveCartier)

local notation "P[" j "]" => D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j)
local notation "C[" j "]" => Additive.ofMul (primeDivisorClass P[j])
local notation "B[" k "," X "]" => Chow.intersectionBilinForm k X

/-- The anticanonical degree of a component in a cycle of length at least two is
its self-intersection plus two. The two incident nodes contribute separately. -/
theorem intersectionBilinForm_anticanonical_boundaryPrime
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K[k,X]) (hn : 1 < n) (j : ZMod n) :
    letI := isNoetherian_of_finiteType g[k,X]
    letI := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    B[k,X] C[j] (Additive.ofMul K[k,X]⁻¹) = B[k,X] C[j] C[j] + 2 := by
  let : IsNoetherian X := isNoetherian_of_finiteType g[k,X]
  let := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  classical
  let : IsReduced D.subscheme :=
    (PrestableFamily.atWorstNodalOfRelativeDimensionOne (f := D.subscheme ↘ S(k))).isReduced
  let q := (A.boundaryPrimeEquiv hD).toEmbedding.trans D.boundaryPrimeEmbedding
  have hq (x : CodimensionOnePoint X) : (x : X) ∈ D.support ↔ x ∈ Set.range q := by
    simp only [q, Function.Embedding.coe_trans, Set.range_comp, Equiv.coe_toEmbedding,
      Equiv.range_eq_univ,
      Set.image_univ, D.range_boundaryPrimeEmbedding]
    rfl
  have hsum := hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass q hq
  rw [hcan] at hsum
  have h1 : (1 : ZMod n) ≠ 0 := fun h ↦ (Nat.ne_of_gt hn) (ZMod.one_eq_zero_iff.mp h)
  have hs : j + 1 ≠ j := by simpa using h1
  have hp : j - 1 ≠ j := by simpa using h1
  have hterm (l : ZMod n) (hl : l ∈ Finset.univ.erase j) :
      B[k,X] C[j] C[l] = (if l = j + 1 then 1 else 0) + (if l = j - 1 then 1 else 0) := by
    rw [A.intersectionBilinForm_boundaryPrime_of_ne hD (Finset.ne_of_mem_erase hl).symm]
    simp only [show j = l + 1 ↔ l = j - 1 from eq_comm.trans eq_sub_iff_add_eq.symm]
  rw [hsum, map_sum]
  simp only [q, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), Finset.sum_congr rfl hterm,
    Finset.sum_add_distrib]
  simp [hs, hp, add_comm]

variable [Scheme.IsRationalOver g[k,X]]

/-- A numbered component of square `-1` in an anticanonical cycle with at least
two components is an exceptional curve of the first kind. -/
theorem isExceptionalCurveOfFirstKind_boundaryPrime_of_selfIntersection
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K[k,X]) (hn : 1 < n) (j : ZMod n)
    (hsq :
      letI := isNoetherian_of_finiteType g[k,X]
      letI := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      B[k,X] C[j] C[j] = -1) :
    letI := isNoetherian_of_finiteType g[k,X]
    (J[(A.boundaryPrimeEquiv hD j).val]).IsExceptionalCurveOfFirstKind := by
  let : IsNoetherian X := isNoetherian_of_finiteType g[k,X]
  let := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  rw [← coe_boundaryPrimeEmbedding D (A.boundaryPrimeEquiv hD j)]
  apply (Chow.isExceptionalCurveOfFirstKind_iff_primeDivisorClass k P[j]).mpr
  have hdeg := A.intersectionBilinForm_anticanonical_boundaryPrime hD hcan hn j
  have hneg : B[k,X] C[j] (Additive.ofMul K[k,X]) = -1 := by
    rw [ofMul_inv, map_neg, hsq] at hdeg
    omega
  simpa only [Chow.intersectionBilinForm_apply, toMul_ofMul] using And.intro hsq hneg

/-- Contract a specified exceptional prime of a numbered anticanonical cycle.
The blowup of the image node recovers the original surface, and the induced map
of boundaries is an oriented subdivision. -/
theorem exists_numbered_nodal_boundary_blowdown [NeZero (2 : k)]
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K[k,X]) (q : D.boundaryPrimes)
    (hE : (J[q.val]).IsExceptionalCurveOfFirstKind) :
    let E := J[q.val]
    ∃ (Y : Scheme.{u}) (s : Y ⟶ S(k)) (f : X ⟶ Y) (p : Y),
      let : Y.Over S(k) := ⟨s⟩
      ∃ (_ : IsIntegral Y) (_ : Y.IsProjectiveOver k) (_ : SmoothOfRelativeDimension 2 g[k,Y]),
        Scheme.IsRationalOver g[k,Y] ∧ f.IsOver S(k) ∧ IsModification f ∧ IsClosed ({p} : Set Y) ∧
        (Y.fromSpecResidueField p).ker.comap f = E ∧
        ∃ e : X ≅ (Y.fromSpecResidueField p).ker.blowup,
          e.hom ≫ (Y.fromSpecResidueField p).ker.blowupToBase = f ∧
          let F := D.map f
          ∃ (hF : F.IsEffectiveCartier) (_ : PrestableFamily (F.subscheme ↘ S(k))),
            LineBundleClass.mk hF.toInvertibleSheaf = K[k,Y] ∧
            F.IsNodeOfReducedBoundary g[k,Y] p ∧
            F.comap f = D * E ∧
            Set.BijOn f (D.boundaryPrimes \ E.support) F.boundaryPrimes ∧
            ∃ (m : ℕ) (_ : NeZero m), n = m + 1 ∧
              ∃ (A' : NodalCycleNumbering
                  (PEmpty.elim : PEmpty.{v + 1} → (F.subscheme ↘ S(k)).smoothLocus) m)
                (a : D.subscheme ⟶ F.subscheme),
                a ≫ F.subschemeι = D.subschemeι ≫ f ∧ a.IsOrientedCycleSubdivision A A' := by
  intro E
  have hED : E.support ≤ D.support := by
    rw [← SetLike.coe_subset_coe, coe_support_vanishingIdeal, Closeds.coe_mk]
    apply closure_minimal _ D.support.isClosed
    exact Set.singleton_subset_iff.mpr (mem_boundaryPrimes.mp q.property).1
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ g[k,X]) := by
    rw [← D.over_eq_subschemeι_comp]
    exact PrestableFamily.atWorstNodalOfRelativeDimensionOne
  obtain ⟨Y, s, f, p, hY, hproj, hsm, hover, hmod, hp, hcenter, hEJ, eJ, heJ,
    _, _, _, hT, _, hbij⟩ := hD.exists_nodal_boundary_blowdown hN hcan hE hED
  let : Y.Over S(k) := ⟨s⟩
  let : IsIntegral Y := hY
  let : Y.IsProjectiveOver k := hproj
  let : SmoothOfRelativeDimension 2 g[k,Y] := hsm
  let : IsModification f := hmod
  let : f.IsOver S(k) := hover
  let I := (Y.fromSpecResidueField p).ker
  have hI : I = J[p] := Y.ker_fromSpecResidueField_eq_vanishingIdeal p
  let e := eJ ≪≫ blowupIso (Iso.refl Y) (hI.symm.trans (comap_id _).symm)
  have he : e.hom ≫ I.blowupToBase = f := by
    simpa only [e, Iso.trans_hom, Category.assoc, blowupIso_hom_blowupToBase,
      Iso.refl_hom, Category.comp_id, toBase_snoc, toBase_nil] using heJ
  have hEI : I.comap f = E := hI.symm ▸ hEJ
  obtain ⟨hF, hpre, hK, htot, m, hm, hlen, A', a, ha, hsub⟩ :=
    hD.exists_numbering_of_exceptional_boundary_contraction A hcan hp e he (hEI ▸ hED)
  have hnode : (D.map f).IsNodeOfReducedBoundary g[k,Y] p := by
    let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g[k,Y]
    apply hT.centre_subset_nodes
    rw [Scheme.Hom.centre_def, ← Scheme.Hom.isoLocus_comp_of_isIso eJ.hom, heJ,
      ← Scheme.Hom.centre_def, hcenter]
    exact Set.mem_singleton p
  obtain ⟨bir, hbir⟩ := IsModification.birationalOver f
  have hBir : BirationalOver g[k,X] g[k,Y] := ⟨bir, by
    simpa only [Category.assoc, Category.comp_id, comp_over f S(k)] using
      congrArg (· ≫ g[k,Y]) hbir⟩
  exact ⟨Y, s, f, p, hY, hproj, hsm, hBir.symm.isRationalOver _ _, hover, hmod, hp, hEI,
    e, he, hF, hpre, hK, hnode, hEI ▸ htot, hbij, m, hm, hlen, A', a, ha, hsub⟩

/-- A square-`-1` component in a numbered anticanonical cycle with at least
two components admits a nodal blowdown. On every surviving component, the
pullback of its image class is the strict class plus its intersection number
with the contracted component times the contracted class. The pullback lattice
is the orthogonal complement of the contracted class. -/
theorem exists_numbered_nodal_boundary_blowdown_of_selfIntersection [NeZero (2 : k)]
    (hcan : LineBundleClass.mk hD.toInvertibleSheaf = K[k,X]) (hn : 1 < n) (j : ZMod n)
    (hsq :
      letI := isNoetherian_of_finiteType g[k,X]
      letI := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
      B[k,X] C[j] C[j] = -1) :
    letI := isNoetherian_of_finiteType g[k,X]
    letI := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let q := A.boundaryPrimeEquiv hD j
    let E := J[q.val]
    ∃ (Y : Scheme.{u}) (s : Y ⟶ S(k)) (f : X ⟶ Y) (p : Y),
      let : Y.Over S(k) := ⟨s⟩
      ∃ (_ : IsIntegral Y) (_ : Y.IsProjectiveOver k) (_ : SmoothOfRelativeDimension 2 g[k,Y]),
        Scheme.IsRationalOver g[k,Y] ∧ f.IsOver S(k) ∧ IsModification f ∧ IsClosed ({p} : Set Y) ∧
        (Y.fromSpecResidueField p).ker.comap f = E ∧
        ∃ e : X ≅ (Y.fromSpecResidueField p).ker.blowup,
          e.hom ≫ (Y.fromSpecResidueField p).ker.blowupToBase = f ∧
          let F := D.map f
          ∃ (hF : F.IsEffectiveCartier) (_ : PrestableFamily (F.subscheme ↘ S(k))),
            LineBundleClass.mk hF.toInvertibleSheaf = K[k,Y] ∧
            F.IsNodeOfReducedBoundary g[k,Y] p ∧ F.comap f = D * E ∧
            Set.BijOn f (D.boundaryPrimes \ E.support) F.boundaryPrimes ∧
            (∃ (m : ℕ) (_ : NeZero m), n = m + 1 ∧
              ∃ (A' : NodalCycleNumbering
                  (PEmpty.elim : PEmpty.{v + 1} → (F.subscheme ↘ S(k)).smoothLocus) m)
                (a : D.subscheme ⟶ F.subscheme),
                a ≫ F.subschemeι = D.subschemeι ≫ f ∧ a.IsOrientedCycleSubdivision A A') ∧
            (∀ L : LineBundleClass X,
              L ∈ Set.range (pullback f) ↔ B[k,X] (Additive.ofMul L) C[j] = 0) ∧
            letI := isNoetherian_of_finiteType g[k,Y]
            letI := g[k,Y].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
            ∀ i : ZMod n, i ≠ j → ∃ r : F.boundaryPrimes,
              f (A.boundaryPrimeEquiv hD i).val = r.val ∧
              Additive.ofMul (pullback f (primeDivisorClass (F.boundaryPrimeEmbedding r))) =
                C[i] + B[k,X] C[i] C[j] • C[j] := by
  let : IsNoetherian X := isNoetherian_of_finiteType g[k,X]
  let := g[k,X].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let q := A.boundaryPrimeEquiv hD j
  have hE := A.isExceptionalCurveOfFirstKind_boundaryPrime_of_selfIntersection hD hcan hn j hsq
  obtain ⟨Y, s, f, p, hY, hproj, hsm, hRat, hf, hmod, hp, hExc, e, he, hF, hpre, hK, hnode,
    htot, hbij, hsub⟩ := A.exists_numbered_nodal_boundary_blowdown hD hcan q hE
  let : Y.Over S(k) := ⟨s⟩
  let : IsIntegral Y := hY
  let : Y.IsProjectiveOver k := hproj
  let : SmoothOfRelativeDimension 2 g[k,Y] := hsm
  let : f.IsOver S(k) := hf
  let : IsNoetherian Y := isNoetherian_of_finiteType g[k,Y]
  let := g[k,Y].uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hExc' : (Y.fromSpecResidueField p).ker.comap f = J[(P[j] : X)] := by
    simpa only [coe_boundaryPrimeEmbedding] using hExc
  refine ⟨Y, s, f, p, hY, hproj, hsm, hRat, hf, hmod, hp, hExc, e, he, hF, hpre, hK, hnode,
    htot, hbij, hsub, ?_, ?_⟩
  · intro L
    have hJ : (J[(P[j] : X)]).IsEffectiveCartier :=
      isEffectiveCartier_vanishingIdeal_closure_singleton (P[j]).property
    rw [Chow.intersectionBilinForm_apply, toMul_ofMul, toMul_ofMul, primeDivisorClass_def]
    exact f.mem_range_pullback_iff_classIntersectionNumber_eq_zero_of_pointBlowdown
      (k := k) hp e he hJ hExc' L
  intro i hij
  let t := A.boundaryPrimeEquiv hD i
  have ht : t.val ∉ (J[q.val]).support := by
    rw [← SetLike.mem_coe, coe_support_vanishingIdeal, Closeds.coe_mk]
    intro h
    have htq := CodimensionOnePoint.eq_of_specializes (x := P[i]) (y := P[j])
      (specializes_iff_mem_closure.mpr (by simpa only [coe_boundaryPrimeEmbedding] using h))
    exact hij ((A.boundaryPrimeEquiv hD).injective (D.boundaryPrimeEmbedding.injective htq.symm))
  let r : (D.map f).boundaryPrimes := ⟨f t.val, hbij.mapsTo ⟨t.property, ht⟩⟩
  refine ⟨r, rfl, ?_⟩
  exact f.pullback_primeDivisorClass_pointBlowdown (k := k) hp e he P[j] P[i]
    ((D.map f).boundaryPrimeEmbedding r) hExc' (by simp only [coe_boundaryPrimeEmbedding, r, t])

end AlgebraicGeometry.Scheme.NodalCycleNumbering
