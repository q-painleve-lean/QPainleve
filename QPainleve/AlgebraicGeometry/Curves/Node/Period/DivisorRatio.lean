/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Period.Basic
public import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import QPainleve.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Period of a difference of Cartier divisors

For two Cartier ideals supported away from the nodes, an identification of their
pullbacks to the normalization trivializes the quotient line bundle there. At the
nodes the inclusions into the structure sheaf give its other trivialization. Its
period is the product of the ratios between the resulting branch scalars. This is
the comparison underlying the point-divisor calculation in [Gross, Hacking and
Keel, *Moduli of surfaces with an anti-canonical cycle*, Proposition 2.9][GHK].

[GHK]: https://arxiv.org/html/1211.6367v5#S2
-/

public noncomputable section

open CategoryTheory MonoidalCategory TauCeti.AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace AlgebraicGeometry.Scheme

open IdealSheafData

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [PrestableFamily (X ↘ Spec (.of k))]
  {ι : Type v} {p : ι → (X ↘ Spec (.of k)).smoothLocus}
  {n : ℕ} [NeZero n]
  {e : ZMod n ≃ (X.dualGraph p).Edge} {o : (X.dualGraph p).Edge → Equiv.Perm (Fin 2)}
  {w : ZMod n ≃ (X.dualGraph p).Vertex}
  (hw : ∀ i b, (X.dualGraph p).endpoint (e i) (o (e i) b) =
    w ((TauCeti.DualGraph.cycle n).endpoint i b))

local notation "ν" => IdealSheafData.blowupToBase (X.singularLocus k)
local notation "i₀" => IdealSheafData.subschemeι (X.singularLocus k)
local notation "j" => X.branchSchemeToBlowup k
local notation "g" => X.branchSchemeToSingularLocus k
local notation "sq" => IsPullback.toCommSq (IsPullback.flip (X.isPullback_branchScheme k))
local notation "nodal" => PrestableFamily.atWorstNodalOfRelativeDimensionOne

variable {I J : X.IdealSheafData} (hI : I.IsEffectiveCartier) (hJ : J.IsEffectiveCartier)
  (hIn : I.comap (Scheme.singularLocus k X).subschemeι = ⊤)
  (hJn : J.comap (Scheme.singularLocus k X).subschemeι = ⊤)
  (a : (pullback (Scheme.singularLocus k X).blowupToBase).obj I.sheaf ≅
    (pullback (Scheme.singularLocus k X).blowupToBase).obj J.sheaf)

local notation "L" => hI.toInvertibleSheaf
local notation "M" => hJ.toInvertibleSheaf
local notation "s" => hI.pullbackTrivializationOfComapEqTop i₀ hIn
local notation "t" => hJ.pullbackTrivializationOfComapEqTop i₀ hJn

/-- The quotient of two Cartier ideal classes identified on the normalization
has multidegree zero. -/
def nodalCartierRatioClass
    (normalizationIso : (pullback ν).obj I.sheaf ≅ (pullback ν).obj J.sheaf) :
    (LineBundleClass.pullbackHom ν).ker :=
  ⟨LineBundleClass.mk L / LineBundleClass.mk M, by
    rw [MonoidHom.mem_ker, map_div, LineBundleClass.pullbackHom_apply,
      LineBundleClass.pullbackHom_apply, LineBundleClass.pullback_mk, LineBundleClass.pullback_mk,
      div_eq_one, LineBundleClass.mk_eq_mk_iff]
    simp only [InvertibleSheaf.pullback_obj_obj, IsEffectiveCartier.toInvertibleSheaf_obj]
    exact ⟨normalizationIso⟩⟩

omit [IsAlgClosed k] in
/-- The underlying Picard class of the Cartier ratio. -/
@[simp]
theorem nodalCartierRatioClass_val :
    (nodalCartierRatioClass (k := k) hI hJ a).val = LineBundleClass.mk L / LineBundleClass.mk M :=
  (rfl)

local notation "b" => s ≪≫ Iso.symm t
local notation "left" => Functor.mapIso (pullback j) a ≪≫ CommSq.pullbackTrivialization sq t
local notation "right" => CommSq.pullbackTrivialization sq s

/-- The branch unit of a Cartier ratio. On the overlap, it compares the pulled-back
normalization isomorphism with the two trivializations given by the ideal inclusions. -/
def nodalCartierRatioUnit
    (hI₀ : I.comap i₀ = ⊤) (hJ₀ : J.comap i₀ = ⊤)
    (normalizationIso : (pullback ν).obj I.sheaf ≅ (pullback ν).obj J.sheaf) :
    Γ(X.branchScheme k, ⊤)ˣ :=
  let u := hI.pullbackTrivializationOfComapEqTop i₀ hI₀
  let v := hJ.pullbackTrivializationOfComapEqTop i₀ hJ₀
  (unitsGlobalSectionsMulEquivAut (𝟙_ (X.branchScheme k).Modules)).symm
    (Aut.of ((CommSq.pullbackTrivialization sq u).symm ≪≫ (pullback j).mapIso normalizationIso ≪≫
      CommSq.pullbackTrivialization sq v))

omit [IsAlgClosed k] in
/-- In the frames given by the inclusions, the pullback of the normalization isomorphism
is multiplication by the Cartier ratio unit. -/
theorem nodalCartierRatioUnit_spec :
    Iso.hom left = Iso.hom right ≫ globalSectionsSmul (𝟙_ (X.branchScheme k).Modules)
      (nodalCartierRatioUnit (k := k) hI hJ hIn hJn a) := by
  rw [nodalCartierRatioUnit, globalSectionsSmul_unitsGlobalSectionsMulEquivAut_symm]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- A branch value of the Cartier ratio is the scalar comparing the two frames on
that branch's rational fiber. This permits computation using local equations on
the normalization components. -/
theorem nodalCartierRatioUnit_branch_eq_iff (z : X.branchScheme k) (v : kˣ) :
    let q := X.branchRationalPoint nodal z
    X.branchSchemeGlobalUnitsEquiv nodal (nodalCartierRatioUnit (k := k) hI hJ hIn hJn a) z = v ↔
      (pullback q).map (Iso.hom left) ≫ (pullbackObjUnitIso q).hom =
        (pullback q).map (Iso.hom right) ≫ (pullbackObjUnitIso q).hom ≫
          globalSectionsSmul (𝟙_ (Spec (.of k)).Modules) ((ΓSpecIso (.of k)).inv v.val) := by
  let q := X.branchRationalPoint nodal z
  let u := nodalCartierRatioUnit (k := k) hI hJ hIn hJn a
  have hq : q ≫ g ≫ i₀ ≫ (X ↘ Spec (.of k)) = 𝟙 _ := by
    simpa only [comp_over] using X.branchRationalPoint_comp nodal z
  have he := X.val_branchSchemeGlobalUnitsEquiv_apply_section nodal u q hq
    (IsLocalRing.closedPoint k)
  have hz : q (IsLocalRing.closedPoint k) = z := X.branchRationalPoint_apply nodal z _
  rw [hz] at he
  dsimp only
  rw [nodalCartierRatioUnit_spec (k := k) hI hJ hIn hJn a, Functor.map_comp, Category.assoc,
    pullback_map_globalSectionsSmul, globalSectionsSmul_naturality]
  simp only [← Category.assoc, cancel_epi]
  constructor
  · intro hv
    have hval := he.symm.trans (congrArg Units.val hv)
    exact congrArg (globalSectionsSmul (𝟙_ (Spec (.of k)).Modules))
      ((Iso.inv_hom_id_apply _ _).symm.trans (congrArg (ΓSpecIso (.of k)).inv hval))
  · intro hv
    have hval := (globalSectionsActionRingEquiv (𝟙_ (Spec (.of k)).Modules)).injective
      (by simpa only [globalSectionsActionRingEquiv_apply] using congrArg End.of hv)
    apply Units.ext
    exact he.trans ((congrArg (ΓSpecIso (.of k)).hom hval).trans (Iso.hom_inv_id_apply _ _))

omit [IsAlgClosed k] in
private theorem pullbackTrivialization_ideal_hom {K : X.IdealSheafData}
    (hK : K.IsEffectiveCartier) (hKn : K.comap i₀ = ⊤) :
    (CommSq.pullbackTrivialization sq (hK.pullbackTrivializationOfComapEqTop i₀ hKn)).hom =
      (pullback j).map ((pullback ν).map K.sheafι ≫ (pullbackObjUnitIso ν).hom) ≫
        (pullbackObjUnitIso j).hom := by
  let φ : K.sheaf ⟶ 𝟙_ X.Modules := K.sheafι
  simp only [CommSq.pullbackTrivialization_hom, ← pullbackObjUnitIso_hom,
    IsEffectiveCartier.pullbackTrivializationOfComapEqTop_hom]
  rw [pullbackComp_inv_app_map_toUnit, ← (pullbackCongr (CommSq.w sq)).hom.naturality_assoc φ,
    pullbackObjUnitIso_congr, ← pullbackComp_inv_app_map_toUnit j ν φ]
  simp only [Iso.hom_inv_id_app_assoc, φ]

/-- Compute the Cartier ratio at a branch by evaluating the normalization isomorphism
and the two ideal inclusions in the branch fiber. -/
theorem nodalCartierRatioUnit_branch_eq_iff_toBlowup (z : X.branchScheme k) (v : kˣ) :
    let q := X.branchRationalPoint nodal z ≫ j
    let inc (K : X.IdealSheafData) :=
      (pullback q).map ((pullback ν).map K.sheafι ≫ (pullbackObjUnitIso ν).hom) ≫
        (pullbackObjUnitIso q).hom
    X.branchSchemeGlobalUnitsEquiv nodal (nodalCartierRatioUnit (k := k) hI hJ hIn hJn a) z = v ↔
      (pullback q).map a.hom ≫ inc J = inc I ≫
        globalSectionsSmul (𝟙_ (Spec (.of k)).Modules) ((ΓSpecIso (.of k)).inv v.val) := by
  let q := X.branchRationalPoint nodal z
  let C := pullbackComp q j
  have hbranch := nodalCartierRatioUnit_branch_eq_iff hI hJ hIn hJn a z v
  dsimp only at hbranch ⊢
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc] at hbranch
  rw [pullbackTrivialization_ideal_hom, pullbackTrivialization_ideal_hom] at hbranch
  rw [hbranch, ← cancel_epi (C.inv.app ((pullback ν).obj I.sheaf))]
  have hn := C.inv.naturality_assoc a.hom
    ((pullback q).map ((pullback j).map
      ((pullback ν).map J.sheafι ≫ (pullbackObjUnitIso ν).hom) ≫
        (pullbackObjUnitIso j).hom) ≫ (pullbackObjUnitIso q).hom)
  simp only [Functor.comp_map] at hn
  rw [← hn, pullbackComp_inv_app_map_toUnit]
  simp only [C, q, Category.assoc, pullbackComp_inv_app_map_toUnit_assoc]

/-- The period of the quotient of two Cartier ideal classes is the oriented product
of the branch ratios of their normalization comparison. Both ideals may have
arbitrary multiplicities away from the nodes. -/
theorem nodalPicardCycleMulEquiv_nodalCartierRatioClass :
    nodalPicardCycleMulEquiv hw (nodalCartierRatioClass (k := k) hI hJ a) =
      X.nodalConductorCycleProduct p e o (nodalCartierRatioUnit (k := k) hI hJ hIn hJn a) := by
  let K := (InvertibleSheaf.dual M).obj
  let c : J.sheaf ⊗ K ≅ 𝟙_ X.Modules :=
    eqToIso (congrArg (· ⊗ K) hJ.toInvertibleSheaf_obj.symm) ≪≫
      InvertibleSheaf.evaluationDualIso M
  let d : (InvertibleSheaf.tensorProduct L (InvertibleSheaf.dual M)).obj ≅ I.sheaf ⊗ K :=
    InvertibleSheaf.tensorProductObjIso L (InvertibleSheaf.dual M) ≪≫
      eqToIso (congrArg (· ⊗ K) hI.toInvertibleSheaf_obj)
  have hInv : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) (I.sheaf ⊗ K) := by
    let E := InvertibleSheaf.tensorProduct L (InvertibleSheaf.dual M)
    have : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) E.obj := E.property
    exact TauCeti.SheafOfModules.IsInvertible.of_iso (R := X.ringCatSheaf) d
  let Q : InvertibleSheaf X := ⟨I.sheaf ⊗ K, hInv⟩
  let f₁ := pullbackTensorRightTrivialization ν a c
  let f₂ := pullbackTensorRightTrivialization i₀ b c
  have hQ : LineBundleClass.mk Q = (nodalCartierRatioClass (k := k) hI hJ a).val := by
    rw [← (LineBundleClass.mk_eq_mk_iff.mpr ⟨d⟩ : LineBundleClass.mk
        (InvertibleSheaf.tensorProduct L (InvertibleSheaf.dual M)) = LineBundleClass.mk Q)]
    simp [div_eq_mul_inv, LineBundleClass.mk_tensorProduct, ← LineBundleClass.inv_mk]
  rw [nodalPicardCycleMulEquiv_apply hw _ Q f₁ f₂ hQ]
  congr 1
  apply (CommSq.lineGluingUnit_tensorRightTrivialization sq a b c _).mpr
  let C := pullbackComp g i₀ ≪≫ pullbackCongr (CommSq.w sq).symm
  let tr := ((pullbackComp j ν).app J.sheaf).symm ≪≫ CommSq.pullbackTrivialization sq t
  apply (cancel_epi ((pullbackComp j ν).hom.app I.sheaf)).mp
  apply (cancel_mono tr.hom).mp
  simp only [Category.assoc]
  rw [globalSectionsSmul_naturality tr.hom]
  have heq {f g' : X.branchScheme k ⟶ X} (h : f = g') :
      (pullbackCongr h.symm).inv = (pullbackCongr h).hom := by
    subst g'
    rfl
  have htr : C.hom.app J.sheaf ≫ tr.hom =
      (pullback g).map (Iso.hom t) ≫ (pullbackObjUnitIso g).hom := by
    simp only [C, tr, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, NatTrans.comp_app,
      CommSq.pullbackTrivialization_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
      ← heq (CommSq.w sq), Iso.hom_inv_id_app_assoc, pullbackObjUnitIso_hom]
  have hu := nodalCartierRatioUnit_spec (k := k) hI hJ hIn hJn a
  simp only [Iso.trans_hom, Functor.mapIso_hom, CommSq.pullbackTrivialization_hom] at hu
  rw [reassoc_of% htr]
  simp only [tr, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.trans_inv, NatTrans.comp_app,
    Category.assoc, Functor.map_comp, CommSq.pullbackTrivialization_hom,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_map_assoc, pullbackObjUnitIso_hom,
    ← heq (CommSq.w sq)]
  rw [← pullbackObjUnitIso_hom g] at hu
  simp only [Category.assoc] at hu
  simpa only [pullbackObjUnitIso_hom, Functor.comp_obj, ← heq (CommSq.w sq)] using hu

end AlgebraicGeometry.Scheme
