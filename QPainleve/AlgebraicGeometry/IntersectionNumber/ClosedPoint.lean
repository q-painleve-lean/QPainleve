/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.IntersectionNumber.Basic
public import TauCeti.AlgebraicGeometry.Curves.Basic
import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.RationalPoint
import TauCeti.AlgebraicGeometry.Curves.Normalization
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.TensorProduct

/-!
# Intersection with a reduced point

The ideal line bundle of a reduced closed point restricts to degree minus the residue degree
on an integral curve containing that point. On a curve avoiding the point it restricts
to the trivial line bundle.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open Scheme.IdealSheafData

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

variable {k : Type u} [Field k] {X C : Scheme.{u}} [C.Over (Spec (.of k))] [C.IsCurveOver k]

/-- The Cartier ideal of a reduced closed point on a proper integral curve has degree
minus the degree of its residue field. -/
theorem eulerDegree_mk_ker_fromSpecResidueField {q : C} (hq : IsClosed ({q} : Set C))
    (hI : (C.fromSpecResidueField q).ker.IsEffectiveCartier) :
    eulerDegree k (mk hI.toInvertibleSheaf) = -((C ↘ Spec (.of k)).residueDegree q : ℤ) := by
  let t := C.fromSpecResidueField q
  let f := (C ↘ Spec (.of k))
  have : IsClosedImmersion t := isClosed_singleton_iff_isClosedImmersion.mp hq
  have : RelativeDimensionLE 1 f :=
    (relativeDimensionLE_iff_of_field _).mpr (Scheme.IsCurveOver.topologicalKrullDim_eq_one k).le
  have : IsFinite (t.ker.subschemeι ≫ f) := hI.isFinite_subschemeι_comp
  have : Flat (t.ker.subschemeι ≫ f) := inferInstance
  have ht : IsFinite (t ≫ f) := by
    rw [← t.toImage_imageι_assoc]
    infer_instance
  have : Module.Finite k (C.residueField q) := by
    rwa [Scheme.fromSpecResidueField_comp_over, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.finite_algebraMap] at ht
  let s : Spec (.of k) := default
  have hdeg : (C ↘ Spec (.of k)).residueDegree q = Module.finrank k (C.residueField q) := by
    rw [Scheme.Hom.residueDegree_eq_finrank, Scheme.residueFieldBaseAlgebra_eq_compHom]
  have hf : (t.ker.subschemeι ≫ f).finrank s = f.residueDegree q := by
    rw [← Scheme.Hom.finrank_comp_left_of_isIso t.toImage,
      t.toImage_imageι_assoc, Scheme.fromSpecResidueField_comp_over, hdeg]
    simpa only [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_def, Nat.cast_id] using
      Scheme.Hom.finrank_SpecMap_algebraMap k (C.residueField q) s
  rw [eulerDegree_mk, hI.eulerDegree_toInvertibleSheaf k _ s, hf]

/-- The ideal class of a reduced closed point restricts to degree minus one on a
proper integral curve through the point and to degree zero off the curve. -/
theorem intersectionNumber_mk_ker_fromSpecResidueField [IsAlgClosed k]
    (e : C ⟶ X) [IsClosedImmersion e] {p : X} (hp : IsClosed ({p} : Set X))
    (hI : (X.fromSpecResidueField p).ker.IsEffectiveCartier)
    [Decidable (p ∈ Set.range e)] :
    intersectionNumber k e (mk hI.toInvertibleSheaf) =
      if p ∈ Set.range e then -1 else 0 := by
  have hclosed (q : C) (h : e q = p) : IsClosed ({q} : Set C) := by
    rw [← e.isClosedEmbedding.injective.preimage_image ({q} : Set C), Set.image_singleton, h]
    exact hp.preimage e.continuous
  have he := hI.comap_of_isIntegral e (by
    rw [← SetLike.mem_coe, Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
    intro h
    have hq := hclosed (genericPoint C) (Set.mem_singleton_iff.mp h)
    have hu := hq.closure_eq.symm.trans (genericPoint_closure C)
    have hs := Set.subsingleton_univ_iff.mp (hu ▸ Set.subsingleton_singleton)
    exact zero_ne_one ((TauCeti.topologicalKrullDim_eq_zero_iff_subsingleton.mpr hs).symm.trans
      (Scheme.IsCurveOver.topologicalKrullDim_eq_one k)))
  rw [intersectionNumber_def, hI.pullback_mk_toInvertibleSheaf he]
  split
  · obtain ⟨q, rfl⟩ := ‹p ∈ Set.range e›
    have hq := hclosed q rfl
    have hcomap := e.comap_ker_fromSpecResidueField_apply q
    have hIq := hcomap ▸ he
    rw [mk_toInvertibleSheaf_congr he hIq hcomap, eulerDegree_mk_ker_fromSpecResidueField hq,
      (C ↘ Spec (.of k)).residueDegree_eq_one_of_isClosed hq, Nat.cast_one]
  · have htop : (X.fromSpecResidueField p).ker.comap e = ⊤ := by
      rw [comap_eq_top_iff, ← Opens.coe_eq_univ, Scheme.Hom.coe_preimage, Closeds.coe_compl,
        Scheme.support_ker_fromSpecResidueField_of_isClosed hp]
      exact Set.eq_univ_of_forall fun q hq ↦ ‹p ∉ Set.range e› ⟨q, hq⟩
    rw [mk_toInvertibleSheaf_congr he (isEffectiveCartier_top C) htop,
      mk_toInvertibleSheaf_top, eulerDegree_one]

end TauCeti.AlgebraicGeometry.LineBundleClass
