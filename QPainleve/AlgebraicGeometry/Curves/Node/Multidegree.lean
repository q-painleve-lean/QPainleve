/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.DualGraph
public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
import QPainleve.AlgebraicGeometry.LineBundle.Clopen
import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections
import TauCeti.AlgebraicGeometry.LineBundle.GenusZero
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk

/-!
# Multidegree zero on rational nodal curves

On a proper nodal curve with genus-zero normalization components over an algebraically
closed field, the multidegree-zero classes are the kernel of pullback to the normalization.
This identifies the domain for the gluing description of `Pic⁰` in Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, Lemma 2.1.
-/

public section

open CategoryTheory TauCeti TauCeti.AlgebraicGeometry TopologicalSpace
open scoped Function

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [PrestableFamily (X ↘ Spec (.of k))]

local notation "ν" => IdealSheafData.blowupToBase (X.singularLocus k)
local notation "N" => IdealSheafData.blowup (X.singularLocus k)
local notation "V" => irreducibleComponents N

/-- A line bundle on a prestable curve whose normalization components have genus zero
pulls back trivially to the normalization exactly when its normalized component degrees
all vanish. -/
theorem pullback_blowupToBase_singularLocus_eq_one_iff [IsAlgClosed k]
    (hgenus : ∀ v : V, (X.blowupComponent v).toScheme.genus k = 0) (a : LineBundleClass X) :
    LineBundleClass.pullback ν a = 1 ↔
      ∀ v : V, LineBundleClass.eulerDegree k
        (LineBundleClass.pullback ((X.blowupComponent v).ι ≫ ν) a) = 0 := by
  classical
  have hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  have : IsRegular N := X.isRegular_blowup_singularLocus hnodal
  have : IsFinite ν := X.isFinite_blowupToBase_singularLocus hnodal
  have hcover : ⨆ v : V, X.blowupComponent v = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr
      ⟨irreducibleComponentOf x, ?_⟩
    simpa only [← SetLike.mem_coe, coe_blowupComponent] using mem_irreducibleComponentOf x
  have hdisj : Pairwise (Disjoint on fun v : V ↦ X.blowupComponent v) := by
    intro v w hvw
    simp only [Function.onFun, ← TopologicalSpace.Opens.coe_disjoint, coe_blowupComponent]
    exact Set.disjoint_left.mpr fun x hxv hxw ↦ hvw
      ((irreducibleComponentOf_eq_iff.mpr hxv).symm.trans
        (irreducibleComponentOf_eq_iff.mpr hxw))
  have hdegree (v : V) (b : LineBundleClass (X.blowupComponent v).toScheme) :
      LineBundleClass.eulerDegree k b = 0 ↔ b = 1 := by
    let C := (X.blowupComponent v).toScheme
    have : IsRegular C := IsRegular.of_isOpenImmersion (X.blowupComponent v).ι
    have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (.of k))
    have hdim (x : C) : Order.coheight x ≤ 1 := by
      exact_mod_cast (coheight_le_topologicalKrullDim x).trans
        (X.topologicalKrullDim_blowupComponent_le_one v)
    exact LineBundleClass.eulerDegree_eq_zero_iff_of_genus_eq_zero hdim
      (C.baseRingToGlobalSections_bijective_of_isIntegrallyClosedIn k
        isIntegrallyClosedIn_of_isAlgClosed).surjective (hgenus v) b
  simp only [← LineBundleClass.pullback_comp, hdegree]
  exact ⟨fun h v ↦ by rw [h, LineBundleClass.pullback_one],
    fun h ↦ LineBundleClass.eq_of_pullback_eq_of_clopenCover hcover hdisj
      (fun v ↦ (h v).trans (LineBundleClass.pullback_one _).symm)⟩

end AlgebraicGeometry.Scheme
