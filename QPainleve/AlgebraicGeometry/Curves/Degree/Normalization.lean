/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Basic
public import TauCeti.AlgebraicGeometry.LineBundle.Degree
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.Normalization.Modification
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import QPainleve.AlgebraicGeometry.Cohomology.OverFiniteScheme
import QPainleve.AlgebraicGeometry.Normalization.Finite
import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Presentation
import TauCeti.AlgebraicGeometry.Cohomology.PushforwardAcyclic.Affine
import TauCeti.AlgebraicGeometry.Curves.Cohomology.Basic
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Finite
import TauCeti.AlgebraicGeometry.Modules.Restriction.FinitePresentation
import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport
import TauCeti.AlgebraicGeometry.Modules.StructureSheafSequence
import TauCeti.AlgebraicGeometry.Normalization.Basic
import TauCeti.AlgebraicGeometry.Normalization.Regular
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.AlgebraicGeometry.VectorBundle.EulerCharacteristic
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Euler degree and normalization of integral curves

The cokernel of `𝒪_C ⟶ ν_* 𝒪_{Cᵛ}` is carried by a closed subscheme finite over the
base field. It contributes the same correction to the Euler characteristics of a line
bundle and of the structure sheaf. Thus the Euler degree of a line bundle on an integral
proper curve can be computed on its normalization.

The comparison uses Tau Ceti's affine pushforward comparison
`Scheme.Hom.cohomologyPushforwardBaseLinearEquivOfIsAffineHom`, projection formula
`FiniteLocallyFreeSheaf.tensorPushforwardUnitIso`, and the semilocal twist calculation
`Scheme.Hom.eulerCharBelow_tensor_pushforward`.

## References

* The Stacks Project, Lemma 33.44.4 (tag 0AYU), birational invariance of degree.
-/

public section

open CategoryTheory Limits MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Hom

noncomputable section

private abbrev structureSheafUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
      (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

private abbrev structureSheafCokernel {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Modules :=
  cokernel (structureSheafUnit f)

private instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    (structureSheafCokernel f).IsQuasicoherent :=
  f.isQuasicoherent_cokernel_unitToPushforwardObjUnit

private theorem isFinitePresentation_structureSheafCokernel {X Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f] :
    (structureSheafCokernel f).IsFinitePresentation := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    isQuasicoherent_structureSheaf X
  have : ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).IsFinitePresentation :=
    isFinitePresentation_pushforward_of_isFinite f _
  exact isFinitePresentation_cokernel (structureSheafUnit f)

private lemma notMem_support_annihilator_structureSheafCokernel {X Y : Scheme.{u}}
    [IsIntegral Y] (f : X ⟶ Y) [IsFinite f] [IsModification f] [IsSchemeTheoreticallyDominant f]
    (h : ∀ U : Y.affineOpens, Module.Finite Γ(Y, U) Γ(structureSheafCokernel f, U)) :
    genericPoint Y ∉ ((structureSheafCokernel f).annihilator h).support := by
  obtain ⟨V, hV, -, hIso⟩ := IsModification.exists_isIso_morphismRestrict (f := f)
  obtain ⟨y, hy⟩ := hV.nonempty
  have hη : genericPoint Y ∈ V :=
    (genericPoint_specializes y).mem_open V.isOpen hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, hUV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hη V.isOpen
  have : IsIso (f ∣_ U) := IsZariskiLocalAtTarget.restrict_of_le
    (MorphismProperty.isomorphisms Scheme) hIso hUV
  have : IsIso (f.app U) := (isIso_morphismRestrict_iff_isIso_app f hU).mp inferInstance
  let η := structureSheafUnit f
  let q := cokernel.π η
  have : @Mono Y.Modules _ _ _ η := f.mono_unitToPushforwardObjUnit
  have : @Epi Y.Modules _ _ _ q :=
    (TauCeti.cokernelSequence_shortExact (C := Y.Modules) η).epi_g
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    isQuasicoherent_structureSheaf X
  have : ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent :=
    isQuasicoherent_pushforward _ f
  have : (cokernel η).IsQuasicoherent :=
    f.isQuasicoherent_cokernel_unitToPushforwardObjUnit
  have hq := Scheme.Modules.Hom.app_surjective_of_epi_of_isAffineOpen q U hU
  have hzero (x : Γ(structureSheafCokernel f, U)) : x = 0 := by
    obtain ⟨t, rfl⟩ := hq x
    obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.app U)).surjective t
    let eval (p : (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⟶
        structureSheafCokernel f) := Scheme.Modules.Hom.app p U s
    have hz := congrArg eval (cokernel.condition η)
    -- The component of the unit on sections is the pullback of regular functions.
    exact hz
  rw [IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hηU, annihilator_ideal]
  have hone : (1 : Γ(Y, U)) ∈ Module.annihilator Γ(Y, U) Γ(structureSheafCokernel f, U) :=
    Module.mem_annihilator.mpr fun x ↦ by simpa using hzero x
  intro hηI
  exact (Y.mem_zeroLocus_iff _ _).mp hηI 1 hone
    (by rw [Scheme.basicOpen_one]; exact hηU)

private lemma isFinite_structureSheafCokernel_support (k : Type u) [Field k]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsCurveOver k]
    (f : X ⟶ Y) [IsFinite f] [IsModification f] [IsSchemeTheoreticallyDominant f]
    (h : ∀ U : Y.affineOpens, Module.Finite Γ(Y, U) Γ(structureSheafCokernel f, U)) :
    IsFinite (((structureSheafCokernel f).annihilator h).subschemeι ≫ Y ↘ Spec (.of k)) := by
  have : IsNoetherian Y := Scheme.IsCurveOver.isNoetherian k Y
  let I := (structureSheafCokernel f).annihilator h
  have hproper : (I.support : Set Y) ≠ Set.univ := by
    intro heq
    have hη : genericPoint Y ∈ (I.support : Set Y) := heq.symm ▸ Set.mem_univ _
    exact notMem_support_annihilator_structureSheafCokernel f h hη
  have hYdim := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k
  have hdim := I.support.isClosed.topologicalKrullDim_lt hproper
    (ne_top_of_le_ne_top (by rw [hYdim]; decide) (topologicalKrullDim_subspace_le Y _))
  rw [hYdim] at hdim
  let i := I.subschemeι
  let e := i.isClosedEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (I.range_subschemeι))
  have hZ : topologicalKrullDim I.subscheme ≤ 0 := by
    rw [e.isHomeomorph.topologicalKrullDim_eq]
    exact Order.le_of_lt_succ hdim
  have : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian i
  have : IsLocallyArtinian I.subscheme := .of_topologicalKrullDim_le_zero hZ
  have : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace i
  have : Finite I.subscheme := finite_of_compact_of_discrete
  let p := i ≫ Y ↘ Spec (.of k)
  have : LocallyOfFiniteType p := inferInstanceAs (LocallyOfFiniteType (i ≫ Y ↘ Spec (.of k)))
  have : LocallyQuasiFinite p := .of_finite_preimage_singleton p fun _ ↦ Set.toFinite _
  exact IsFinite.of_locallyQuasiFinite p

private theorem exists_structureSheafCokernel_iso_pushforward (k : Type u) [Field k]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsCurveOver k]
    (f : X ⟶ Y) [IsFinite f] [IsModification f] [IsSchemeTheoreticallyDominant f] :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ Y) (_ : IsClosedImmersion i)
      (_ : IsFinite (i ≫ Y ↘ Spec (.of k))) (G : Z.Modules),
      G.IsFinitePresentation ∧ Nonempty (structureSheafCokernel f ≅ (pushforward i).obj G) := by
  have : IsNoetherian Y := Scheme.IsCurveOver.isNoetherian k Y
  let Q := structureSheafCokernel f
  have : Q.IsFinitePresentation := f.isFinitePresentation_structureSheafCokernel
  have : Q.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation Q
  let hQ (U : Y.affineOpens) := Q.finite_sections_of_isAffineOpen U.val U.property
  let I := Q.annihilator hQ
  let i := I.subschemeι
  have : IsIso ((pullbackPushforwardAdjunction i).unit.app Q) :=
    isIso_unit_app_of_ker_ideal_le_annihilator i Q fun U ↦ by
      rw [I.ker_subschemeι, Q.annihilator_ideal hQ]
  let G := (Scheme.Modules.pullback i).obj Q
  let e : Q ≅ (pushforward i).obj G := asIso ((pullbackPushforwardAdjunction i).unit.app Q)
  exact ⟨I.subscheme, i, inferInstance, isFinite_structureSheafCokernel_support k f hQ,
    G, isFinitePresentation_pullback i Q, ⟨e⟩⟩

private theorem isCurveOver_normalization (k : Type u) [Field k]
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsCurveOver k]
    [IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization] :
    letI : (Y.fromSpecStalk (genericPoint Y)).normalization.Over (Spec (.of k)) :=
      ⟨(Y.fromSpecStalk (genericPoint Y)).fromNormalization ≫ Y ↘ Spec (.of k)⟩
    (Y.fromSpecStalk (genericPoint Y)).normalization.IsCurveOver k := by
  let ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  let X := (Y.fromSpecStalk (genericPoint Y)).normalization
  let p := ν ≫ Y ↘ Spec (.of k)
  let : X.Over (Spec (.of k)) := ⟨p⟩
  have hp : IsProper (ν ≫ Y ↘ Spec (.of k)) := inferInstance
  have : IsProper (X ↘ Spec (.of k)) := hp
  have : LocallyOfFiniteType p := IsProper.toLocallyOfFiniteType
  have : IsIntegral X := by dsimp only [X]; infer_instance
  obtain ⟨U, hU, hV, hIso⟩ := IsModification.exists_isIso_morphismRestrict (f := ν)
  have : Nonempty ↥(U : Set Y) := hU.nonempty.coe_sort
  have : Nonempty ↥((ν ⁻¹ᵁ U : X.Opens) : Set X) := hV.nonempty.coe_sort
  refine ⟨?_⟩
  calc
    topologicalKrullDim X = topologicalKrullDim (ν ⁻¹ᵁ U) :=
      (topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType p
        (ν ⁻¹ᵁ U).isOpen.isOpenEmbedding_subtypeVal).symm
    _ = topologicalKrullDim U :=
      (asIso (ν ∣_ U)).hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    _ = topologicalKrullDim Y :=
      topologicalKrullDim_eq_of_isOpenEmbedding_of_locallyOfFiniteType
        (Y ↘ Spec (.of k)) (Y := ↥(U : Set Y)) U.isOpen.isOpenEmbedding_subtypeVal
    _ = 1 := Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k

end

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

open _root_.AlgebraicGeometry

noncomputable section

private theorem eulerCharBelow_eq_add_of_tensor_structureSheafCokernel (k : Type u) [Field k]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsCurveOver k]
    (f : X ⟶ Y) [IsFinite f] [IsModification f] [IsSchemeTheoreticallyDominant f]
    (L : InvertibleSheaf Y) {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    (e₃ : S.X₃ ≅ L.obj ⊗ Scheme.Hom.structureSheafCokernel f)
    (hfin : ∀ n < 2, FiniteDimensional k (Cohomology S.X₂ n))
    (hvan : Subsingleton (Cohomology S.X₂ 2)) :
    eulerCharBelow k Y S.X₂ 2 = eulerCharBelow k Y S.X₁ 2 +
      eulerCharBelow k Y (Scheme.Hom.structureSheafCokernel f) 2 := by
  obtain ⟨Z, i, _, hi, G, hG, ⟨eQ⟩⟩ :=
    Scheme.Hom.exists_structureSheafCokernel_iso_pushforward k f
  have : G.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation G
  let : Z.Over (Spec (.of k)) := ⟨i ≫ Y ↘ Spec (.of k)⟩
  let : i.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsFinite (Z ↘ Spec (.of k)) := hi
  have : IsAffine Z := isAffine_of_isAffineHom (Z ↘ Spec (.of k))
  have : IsLocallyArtinian Z := IsLocallyArtinian.of_locallyQuasiFinite (Z ↘ Spec (.of k))
  have : IsArtinianRing Γ(Z, ⊤) := IsLocallyArtinian.isArtinianRing_of_isAffine
  let E := (toFiniteLocallyFree Y).obj L
  let e : S.X₃ ≅ (Scheme.Modules.pushforward i).obj
      (((FiniteLocallyFreeSheaf.pullback i).obj E).obj ⊗ G) :=
    e₃ ≪≫ tensorIso (Iso.refl L.obj) eQ ≪≫
      (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso i E).app G
  have hg₃ : (((FiniteLocallyFreeSheaf.pullback i).obj E).obj ⊗ G).IsFiniteType := by
    have : G.IsFinitePresentation := hG
    let F := ((FiniteLocallyFreeSheaf.pullback i).obj E).obj
    obtain ⟨P, hP⟩ := F.exists_isFinite_presentation_of_isAffine
    obtain ⟨R, hR⟩ := G.exists_isFinite_presentation_of_isAffine
    have : (P.tensor R).IsFinite :=
      SheafOfModules.Presentation.isFinite_tensor (R := Z.sheaf) P R
    have : (F ⊗ G).IsFinitePresentation := (P.tensor R).isFinitePresentation
    exact SheafOfModules.instIsFiniteTypeOfIsFinitePresentation (F ⊗ G)
  have h := eulerCharBelow_eq_add_of_finite_quotient k i hS _ e hfin hvan
  have h₃ : eulerCharBelow k Y S.X₃ 2 =
      eulerCharBelow k Y (Scheme.Hom.structureSheafCokernel f) 2 := by
    have htwist := i.eulerCharBelow_tensor_pushforward k ((toFixedRankOne Y).obj L) G 2
    rw [Nat.cast_one, one_mul, toFixedRankOne_obj_obj] at htwist
    have hE : ((toFiniteLocallyFree Y).obj L).obj = L.obj := (rfl)
    rw [hE] at htwist
    exact (eulerCharBelow_congr k (e₃ ≪≫ tensorIso (Iso.refl L.obj) eQ) 2).trans
      (htwist.trans (eulerCharBelow_congr k eQ 2).symm)
  rwa [h₃] at h

private theorem eulerCharBelow_pushforwardObjUnit_eq_add (k : Type u) [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [X.IsCurveOver k] [Y.IsCurveOver k]
    [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
    (f : X ⟶ Y) [IsFinite f] [IsModification f] [IsSchemeTheoreticallyDominant f]
    [f.IsOver (Spec (.of k))] (L : InvertibleSheaf Y) :
    eulerCharBelow k X ((pullback f).obj L).obj 2 = eulerCharBelow k Y L.obj 2 +
      eulerCharBelow k Y (Scheme.Hom.structureSheafCokernel f) 2 := by
  have : IsNoetherian Y := Scheme.IsCurveOver.isNoetherian k Y
  have : MonoidalPreadditive Y.Modules := TauCeti.SheafOfModules.monoidalPreadditive Y.sheaf
  let E := (toFiniteLocallyFree Y).obj L
  have : L.obj.IsLocallyFree := E.property.1
  have : L.obj.IsFinitePresentation := E.property.2
  have : L.obj.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation L.obj
  let S₀ : ShortComplex Y.Modules :=
    ShortComplex.cokernelSequence (Scheme.Hom.structureSheafUnit f)
  let S : ShortComplex Y.Modules := S₀.map (tensorLeft L.obj)
  have : @Mono Y.Modules _ _ _ (Scheme.Hom.structureSheafUnit f) :=
    f.mono_unitToPushforwardObjUnit
  have hS₀ : S₀.ShortExact := TauCeti.cokernelSequence_shortExact _
  have hS : S.ShortExact := shortExact_map_tensorLeft L.obj hS₀
  let e₁ : S.X₁ ≅ L.obj := ρ_ L.obj
  let e₂ : S.X₂ ≅ (Scheme.Modules.pushforward f).obj ((pullback f).obj L).obj :=
    FiniteLocallyFreeSheaf.tensorPushforwardUnitIso f E ≪≫
      (Scheme.Modules.pushforward f).mapIso (eqToIso (by
        rw [FiniteLocallyFreeSheaf.pullback_obj_obj, pullback_obj_obj]
        rfl))
  have hc (n : ℕ) := (cohomologyBaseLinearEquivOfIso k e₂ n).trans
    (f.cohomologyPushforwardBaseLinearEquivOfIsAffineHom k ((pullback f).obj L).obj n)
  have : ((pullback f).obj L).obj.IsFiniteType := by
    rw [pullback_obj_obj]
    exact isFiniteType_pullback f L.obj
  have hfin (n : ℕ) : FiniteDimensional k (Cohomology S.X₂ n) :=
    have := finiteDimensional_cohomology_of_isCurveOver k ((pullback f).obj L).obj n
    Module.Finite.equiv (hc n).symm
  have hvan : Subsingleton (Cohomology S.X₂ 2) :=
    have := subsingleton_cohomology_of_two_le_of_isCurveOver k ((pullback f).obj L).obj 2 le_rfl
    (hc 2).toEquiv.subsingleton
  have h₂ : eulerCharBelow k Y S.X₂ 2 = eulerCharBelow k X ((pullback f).obj L).obj 2 := by
    rw [eulerCharBelow_two, eulerCharBelow_two, (hc 0).finrank_eq, (hc 1).finrank_eq]
  rw [← h₂, ← eulerCharBelow_congr k e₁ 2]
  exact eulerCharBelow_eq_add_of_tensor_structureSheafCokernel k f L hS
    (Iso.refl _) (fun n _ ↦ hfin n) hvan

/-- Pullback to the normalization preserves the Euler degree of a line bundle on a proper
integral curve over a field. -/
theorem eulerDegree_pullback_normalization (k : Type u) [Field k]
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsCurveOver k] (L : InvertibleSheaf Y) :
    let ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
    letI : (Y.fromSpecStalk (genericPoint Y)).normalization.Over (Spec (.of k)) :=
      ⟨ν ≫ Y ↘ Spec (.of k)⟩
    ((pullback ν).obj L).eulerDegree k = L.eulerDegree k := by
  let ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  let X := (Y.fromSpecStalk (genericPoint Y)).normalization
  let : X.Over (Spec (.of k)) := ⟨ν ≫ Y ↘ Spec (.of k)⟩
  let : ν.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : IsFinite ν :=
    Scheme.Hom.isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
      (Y ↘ Spec (.of k))
  have : X.IsCurveOver k := Scheme.Hom.isCurveOver_normalization k
  have : IsNoetherian Y := Scheme.IsCurveOver.isNoetherian k Y
  have : IsRegular X := isRegular_normalization_fromSpecStalk_genericPoint
    (Scheme.IsCurveOver.topologicalKrullDim_eq_one (X := Y) k).le
  have (x : CodimensionOnePoint X) : IsDiscreteValuationRing (X.presheaf.stalk (x : X)) :=
    inferInstance
  have : IsSchemeTheoreticallyDominant (Y.fromSpecStalk (genericPoint Y)) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsSchemeTheoreticallyDominant ν :=
    Scheme.Hom.isSchemeTheoreticallyDominant_fromNormalization _
  have hL := eulerCharBelow_pushforwardObjUnit_eq_add k ν L
  have hO := eulerCharBelow_pushforwardObjUnit_eq_add k ν (trivial Y)
  obtain ⟨e⟩ : Nonempty (((pullback ν).obj (trivial Y)).obj ≅ (trivial X).obj) := by
    rw [← LineBundleClass.mk_eq_mk_iff, ← LineBundleClass.pullback_mk]
    rw [LineBundleClass.mk_trivial, LineBundleClass.pullback_one, LineBundleClass.mk_trivial]
  -- Reduce the let-bound normalization map and base structure before rewriting the degree.
  change ((pullback ν).obj L).eulerDegree k = L.eulerDegree k
  rw [eulerDegree_def, eulerDegree_def, hL, ← eulerCharBelow_congr k e 2, hO]
  abel

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry

/-- The degree of a line-bundle class on a proper integral curve can be computed on its
normalization. -/
@[simp]
theorem eulerDegree_pullback_normalization (k : Type u) [Field k]
    {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Y.IsCurveOver k] (a : LineBundleClass Y) :
    let ν := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
    letI : (Y.fromSpecStalk (genericPoint Y)).normalization.Over (Spec (.of k)) :=
      ⟨ν ≫ Y ↘ Spec (.of k)⟩
    eulerDegree k (pullback ν a) = eulerDegree k a := by
  obtain ⟨L, rfl⟩ := mk_surjective a
  dsimp only
  rw [pullback_mk, eulerDegree_mk, eulerDegree_mk]
  exact InvertibleSheaf.eulerDegree_pullback_normalization k L

end TauCeti.AlgebraicGeometry.LineBundleClass
