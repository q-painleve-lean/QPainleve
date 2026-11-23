/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Normalization
public import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.Basic

import QPainleve.AlgebraicGeometry.Blowup.Conductor
import QPainleve.AlgebraicGeometry.IdealSheaf.Stalk
import QPainleve.RingTheory.Ideal.AffineBlowup.Conductor
import TauCeti.AlgebraicGeometry.IdealSheaf.Conductor.BaseChange

/-!
# The conductor of a nodal curve

The conductor of the finite blowup separating the branches of a nodal curve is
the ideal sheaf of the singular subscheme. Thus the conductor subschemes on the
curve and the blowup are the node and branch schemes, respectively.

The local calculation uses Tau Ceti's tangent-cone description of the blowup
chart at a node, following the localization argument in
`TauCeti/AlgebraicGeometry/Curves/Node/Blowup.lean`. The quadratic relation on the
generators puts the maximal ideal in the conductor. The closed fiber has rank two,
so the conductor is proper.
See [Stacks Project, Lemma 53.19.4](https://stacks.math.columbia.edu/tag/0C4A).
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry KaehlerDifferential IsLocalRing reesAlgebra
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

private theorem map_singularLocus_ideal_eq_maximalIdeal
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) (U : X.affineOpens)
    (q : Ideal Γ(X, U)) [q.IsPrime]
    (hq : letI := hnodal.syntomic; (X.singularLocus k).ideal U ≤ q) :
    letI := hnodal.syntomic
    ((X.singularLocus k).ideal U).map (algebraMap Γ(X, U) (Localization.AtPrime q)) =
      maximalIdeal (Localization.AtPrime q) := by
  let := hnodal.syntomic
  let A := Γ(X, U)
  let : Algebra k A := ((X.baseRingToStructurePresheaf k).app (op U.val)).hom.toAlgebra
  let R := Localization.AtPrime q
  have : Algebra.FiniteType k A := finiteType_sections_of_locallyOfFiniteType k X U
  have : Algebra.EssFiniteType A R := .of_isLocalization R q.primeCompl
  have : Algebra.EssFiniteType k R := .comp k A R
  have hfit := X.singularLocus_ideal (R := k) U
  have : Algebra.FormallyUnramified k (A ⧸ fittingIdeal A Ω[A⁄k] 1) :=
    hfit ▸ X.formallyUnramified_quotient_singularLocus_ideal hnodal U
  have : Algebra.FormallyUnramified k (R ⧸ fittingIdeal R Ω[R⁄k] 1) :=
    formallyUnramified_localization_quotient_fittingIdeal q.primeCompl
  have hloc := (KaehlerDifferential.isBaseChange_of_formallyEtale k A R).fittingIdeal_eq_map 1
  rw [hfit, ← hloc]
  apply Ideal.eq_maximalIdeal_of_formallyUnramified_quotient k
  rw [hloc, ← hfit]
  exact ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top
    ((Ideal.map_mono hq).trans Localization.AtPrime.map_eq_maximalIdeal.le)

private theorem conductor_comap_Spec_localization_eq_of_node
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) (U : X.affineOpens)
    (q : Ideal Γ(X, U)) [q.IsPrime]
    (hq : letI := hnodal.syntomic; (X.singularLocus k).ideal U ≤ q)
    (e : U.val ≤ (X ↘ Spec (.of k)) ⁻¹ᵁ ⊤)
    (hstd : IsStandardSyntomicOfRelativeDimension 1 ((X ↘ Spec (.of k)).appLE ⊤ U e).hom) :
    letI := hnodal.syntomic
    letI := X.isFinite_blowupToBase_singularLocus hnodal
    let g := Spec.algebraMap Γ(X, U) (Localization.AtPrime q) ≫ U.property.fromSpec
    (X.singularLocus k).blowupToBase.conductor.comap g = (X.singularLocus k).comap g := by
  let := hnodal.syntomic
  let := X.isFinite_blowupToBase_singularLocus hnodal
  let J := X.singularLocus k
  let A := Γ(X, U)
  let : Algebra k A := ((X.baseRingToStructurePresheaf k).app (op U.val)).hom.toAlgebra
  have : Algebra.IsStandardSyntomicOfRelativeDimension 1 k A := by
    refine (isStandardSyntomicOfRelativeDimension_iff 1 _).mp ?_
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
    exact (isStandardSyntomicOfRelativeDimension_respectsIso 1).right _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hstd
  obtain ⟨ι, σ, _, _, P, hcard⟩ :=
    Algebra.IsStandardSyntomicOfRelativeDimension.exists_presentation (n := 1) (R := k) (S := A)
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  have hP : Fintype.card σ + 1 = Fintype.card ι := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard, add_comm]
  have : Algebra.FinitePresentation k A :=
    Algebra.IsStandardSyntomicOfRelativeDimension.finitePresentation (n := 1)
  have hfit := X.singularLocus_ideal (R := k) U
  have : Algebra.FormallyUnramified k (A ⧸ fittingIdeal A Ω[A⁄k] 1) :=
    hfit ▸ X.formallyUnramified_quotient_singularLocus_ideal hnodal U
  obtain ⟨a, b, hab, hb, hr, -⟩ :=
    P.exists_etale_tensor_affineBlowup_of_formallyUnramified hP q (hfit ▸ hq)
  have hmax := map_singularLocus_ideal_eq_maximalIdeal hnodal U q hq
  have hc := Ideal.conductor_affineBlowup_eq_maximalIdeal hab.symm hb (by rw [hr]; decide)
  have hloc := J.conductor_comap_Spec_algebraMap_fromSpec_eq_of_span_pair U
    (A := Localization.AtPrime q) (hab.symm.trans hmax.symm) (hmax ▸ hb)
  simp only [Spec.algebraMap] at hloc
  rw [hmax, hc, ← hmax] at hloc
  let φ := CommRingCat.ofHom (algebraMap A (Localization.AtPrime q))
  exact hloc.trans (IdealSheafData.comap_SpecMap_fromSpec_eq_ofIdealTop J U.property φ).symm

private theorem conductor_comap_fromSpecStalk_eq_of_node
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) (x : X)
    (hx : letI := hnodal.syntomic; x ∈ (X.singularLocus k).support) :
    letI := hnodal.syntomic
    letI := X.isFinite_blowupToBase_singularLocus hnodal
    (X.singularLocus k).blowupToBase.conductor.comap (X.fromSpecStalk x) =
      (X.singularLocus k).comap (X.fromSpecStalk x) := by
  let := hnodal.syntomic
  let := X.isFinite_blowupToBase_singularLocus hnodal
  obtain ⟨U, hxU, e, hstd⟩ :=
    SyntomicOfRelativeDimension.exists_isStandardSyntomicOfRelativeDimension_appLE_top 1
      (X ↘ Spec (.of k)) x
  let J := X.singularLocus k
  let A := Γ(X, U)
  let q := (U.property.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hq : J.ideal U ≤ q := by
    rw [IdealSheafData.mem_support_iff_of_mem hxU, Scheme.mem_zeroLocus_iff] at hx
    simpa only [U.property.mem_basicOpen_iff_notMem_primeIdealOf ⟨x, hxU⟩, not_not,
      SetLike.mem_coe, ← IsConcreteLE.le_iff] using hx
  have hloc := conductor_comap_Spec_localization_eq_of_node hnodal U q hq e hstd
  let φ := CommRingCat.ofHom (algebraMap A (Localization.AtPrime q))
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  let := U.property.isLocalization_stalk ⟨x, hxU⟩
  let t := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (X.presheaf.stalk x)
  let ψ := Spec.map (CommRingCat.ofHom t.toRingHom)
  have hg : X.fromSpecStalk x = ψ ≫ Spec.map φ ≫ U.property.fromSpec := by
    rw [← U.property.fromSpecStalk_eq_fromSpecStalk hxU]
    unfold IsAffineOpen.fromSpecStalk
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    exact (t.commutes r).symm
  rw [hg]
  simpa only [IdealSheafData.comap_comp] using
    congrArg (fun I : (Spec (.of (Localization.AtPrime q))).IdealSheafData ↦ I.comap ψ) hloc

/-- The conductor of the finite blowup that separates a nodal curve's branches is
its singular ideal sheaf. This holds over any field, including at nonsplit nodes. -/
theorem conductor_blowupToBase_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) :
    letI := hnodal.syntomic
    letI := X.isFinite_blowupToBase_singularLocus hnodal
    (X.singularLocus k).blowupToBase.conductor = X.singularLocus k := by
  let := hnodal.syntomic
  let := X.isFinite_blowupToBase_singularLocus hnodal
  let J := X.singularLocus k
  let f := J.blowupToBase
  apply IdealSheafData.eq_of_comap_fromSpecStalk_eq
  intro x
  by_cases hx : x ∈ J.support
  · exact conductor_comap_fromSpecStalk_eq_of_node hnodal x hx
  have hxs : x ∈ (X ↘ Spec (.of k)).smoothLocus := by
    simpa only [J, mem_support_singularLocus_iff_notMem_smoothLocus, not_not] using hx
  let W := (X ↘ Spec (.of k)).smoothLocus
  have : IsIso (f ∣_ W) := X.isIso_blowupToBase_singularLocus_restrict_smoothLocus (R := k)
  have hW : Set.range (X.fromSpecStalk x) ⊆ Set.range W.ι := by
    rw [Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
    exact fun _ hy ↦ hy.mem_open W.isOpen hxs
  let g := IsOpenImmersion.lift W.ι (X.fromSpecStalk x) hW
  rw [← IsOpenImmersion.lift_fac W.ι (X.fromSpecStalk x) hW,
    IdealSheafData.comap_comp, IdealSheafData.comap_comp]
  congr 1
  have hpb := (isPullback_morphismRestrict f W).flip
  have : IsFinite (f ∣_ W) := MorphismProperty.of_isPullback hpb inferInstance
  rw [← Hom.conductor_eq_comap_of_isPullback hpb,
    (Hom.conductor_eq_top_iff _).mpr inferInstance]
  rw [eq_comm, ← IdealSheafData.support_eq_bot_iff, IdealSheafData.support_comap]
  apply SetLike.ext'
  rw [TopologicalSpace.Closeds.coe_preimage, TopologicalSpace.Closeds.coe_bot]
  exact Set.eq_empty_iff_forall_notMem.mpr fun y hy ↦
    ((X.mem_support_singularLocus_iff_notMem_smoothLocus (R := k) y.val).mp hy) y.property

end AlgebraicGeometry.Scheme
