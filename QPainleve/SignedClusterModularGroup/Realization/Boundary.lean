/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.GenericPoint
public import QPainleve.AlgebraicGeometry.IdealSheaf.Boundary.Primes
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry
public import QPainleve.SignedClusterModularGroup.Realization.Basic

import QPainleve.AlgebraicGeometry.Curves.Node.BoundaryRestriction
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Dimension
import QPainleve.AlgebraicGeometry.IdealSheaf.Image.Over

/-!
# Boundary classes of geometric realizations

The generic points of a numbered nodal Cartier boundary give prime divisor classes
in the marked Picard lattice. A pair isomorphism acts forward on those points and
pulls their classes back along the inverse permutation. Thus a geometric realization
between fibers of a fixed boundary marking gives a signed boundary isometry, or a
boundary rotation when the action preserves orientation.

The pullback calculation uses `LineBundleClass.pullback_primeDivisorClass_mapOfIsOpenImmersion`
on the ambient surface isomorphism.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory DihedralGroup Order TauCeti.AlgebraicGeometry
open Scheme Scheme.IdealSheafData

universe u

namespace QPainleve.SignedClusterModularGroup

variable {k : Type u} [Field k] [IsSepClosed k] [Infinite k] {n : ℕ} [NeZero n]
  {L₀ L₁ : Type u} [AddCommGroup L₀] [AddCommGroup L₁]
  {B₀ : LinearMap.BilinForm ℤ L₀} {B₁ : LinearMap.BilinForm ℤ L₁}
  {X₀ X₁ : Scheme.{u}} {M : MarkedSurface k n B₀ X₀} {N : MarkedSurface k n B₁ X₁}

local notation "S" => Spec (CommRingCat.of k)

local notation "D[" P "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair P)))

namespace MarkedSurface

variable (M)

/-- The ambient codimension-one point of the numbered component of a Cartier boundary. -/
def boundaryPrime (hM : M.pair.hom.left.ker.IsEffectiveCartier) (j : ZMod n) :
    CodimensionOnePoint M.surface := by
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let : IsClosedImmersion M.pair.hom.left := M.closedImmersion
  let f := M.pair.hom.left
  let x := M.cycle.componentGenericPoint j
  have hx : coheight x = 0 := by
    dsimp only [x]
    rw [M.cycle.componentGenericPoint_def]
    exact M.boundary.coheight_blowupComponentGeneric (M.cycle.component j)
  have hxi : coheight (f.toImage x) = 0 :=
    (coheight_eq_of_isOpenImmersion f.toImage (x := x)).trans hx
  have hf : f.imageι (f.toImage x) = f x := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
  exact ⟨f x, hf ▸ hM.coheight_subschemeι_of_coheight_eq_zero hxi⟩

/-- On underlying points the boundary prime is the image of the component's generic point. -/
@[simp]
theorem coe_boundaryPrime (hM : M.pair.hom.left.ker.IsEffectiveCartier) (j : ZMod n) :
    letI : PrestableFamily (M.boundary ↘ S) := M.prestable
    (M.boundaryPrime hM j : M.surface) = M.pair.hom.left (M.cycle.componentGenericPoint j) :=
  (rfl)

/-- Each numbered boundary prime belongs to the set of primes of the boundary ideal. -/
theorem boundaryPrime_mem_boundaryPrimes (hP : D[M].IsEffectiveCartier) (j : ZMod n) :
    (M.boundaryPrime hP j : M.surface) ∈ D[M].boundaryPrimes := by
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let : IsClosedImmersion M.pair.hom.left := M.closedImmersion
  refine mem_boundaryPrimes.mpr ⟨?_, (M.boundaryPrime hP j).property⟩
  have hs : (D[M].support : Set M.surface) = Set.range M.pair.hom.left :=
    M.pair.hom.left.support_ker.trans M.pair.hom.left.isClosedEmbedding.isClosed_range.closure_eq
  rw [M.coe_boundaryPrime]
  rw [← SetLike.mem_coe, hs]
  exact Set.mem_range_self _

/-- The numbering of a marked Cartier boundary as an embedding into its ambient primes. -/
def numberedBoundaryPrimes (hM : D[M].IsEffectiveCartier) : ZMod n ↪ D[M].boundaryPrimes where
  toFun j := ⟨M.boundaryPrime hM j, M.boundaryPrime_mem_boundaryPrimes hM j⟩
  inj' := by
    let : PrestableFamily (M.boundary ↘ S) := M.prestable
    let : IsClosedImmersion M.pair.hom.left := M.closedImmersion
    intro j l h
    apply M.cycle.componentGenericPoint_injective
    apply M.pair.hom.left.isClosedEmbedding.injective
    simpa only [coe_boundaryPrime] using congrArg Subtype.val h

/-- The prime at a numbered component is the ambient image of its generic point. -/
@[simp]
theorem numberedBoundaryPrimes_apply_val (hM : D[M].IsEffectiveCartier) (j : ZMod n) :
    (M.numberedBoundaryPrimes hM j).val = (M.boundaryPrime hM j : M.surface) :=
  (rfl)

/-- The class of the numbered prime divisor in the fixed Picard marking. -/
def boundaryClass (hM : M.pair.hom.left.ker.IsEffectiveCartier) (j : ZMod n) : L₀ :=
  letI : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  letI := (M.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  M.picardMarking.symm (Additive.ofMul (LineBundleClass.primeDivisorClass (M.boundaryPrime hM j)))

/-- The Picard marking sends the numbered boundary class to the class of its prime divisor. -/
@[simp]
theorem picardMarking_boundaryClass (hM : M.pair.hom.left.ker.IsEffectiveCartier) (j : ZMod n) :
    letI : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
    letI := (M.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    M.picardMarking (M.boundaryClass hM j) =
      Additive.ofMul (LineBundleClass.primeDivisorClass (M.boundaryPrime hM j)) := by
  simp [boundaryClass]

/-- Under a pair isomorphism, the ambient prime follows the forward dihedral action. -/
theorem map_boundaryPrime (hM : M.pair.hom.left.ker.IsEffectiveCartier)
    (hN : N.pair.hom.left.ker.IsEffectiveCartier) (e : M.pair ≅ N.pair) (j : ZMod n) :
    letI : PrestableFamily (M.boundary ↘ S) := M.prestable
    letI : PrestableFamily (N.boundary ↘ S) := N.prestable
    CodimensionOnePoint.mapOfIsOpenImmersion (surfaceIso e).hom (M.boundaryPrime hM j) =
      N.boundaryPrime hN
        (cycleVertexPerm ((boundaryIso e).boundaryCycleAction M.cycle N.cycle) j) := by
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let : PrestableFamily (N.boundary ↘ S) := N.prestable
  apply Subtype.ext
  simp only [CodimensionOnePoint.coe_mapOfIsOpenImmersion, coe_boundaryPrime]
  rw [← Scheme.Hom.comp_apply, ← boundaryIso_hom_comp, Scheme.Hom.comp_apply]
  exact congrArg N.pair.hom.left ((boundaryIso e).apply_componentGenericPoint M.cycle N.cycle j)

section BoundaryImage

variable (P : MarkedSurface k n B₀ X₀)

/-- The specified closed boundary identifies with the subscheme cut out by its ideal. -/
def boundaryImageIso : P.boundary ≅ D[P].subscheme :=
  letI : IsClosedImmersion P.pair.hom.left := P.closedImmersion
  asIso P.pair.hom.left.toImage

@[reassoc]
theorem boundaryImageIso_hom_comp :
    (boundaryImageIso P).hom ≫ D[P].subschemeι = P.pair.hom.left :=
  P.pair.hom.left.toImage_imageι

instance :
    (boundaryImageIso P).hom.IsOver (Spec (.of k)) := by
  constructor
  rw [over_eq_subschemeι_comp, boundaryImageIso_hom_comp_assoc]
  exact Over.w P.pair.hom

/-- The subscheme cut out by the ideal of a marked surface's boundary is prestable. -/
theorem prestable_boundaryImage : PrestableFamily (D[P].subscheme ↘ Spec (.of k)) := by
  have h : (boundaryImageIso P).hom ≫ (D[P].subscheme ↘ Spec (.of k)) =
      (P.boundary ↘ Spec (.of k)) := HomIsOver.comp_over
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @PrestableFamily)
    (boundaryImageIso P).hom _).mp (h.symm ▸ P.prestable)

local instance : PrestableFamily (D[P].subscheme ↘ S) := P.prestable_boundaryImage

/-- The marked cycle numbering transported to the subscheme cut out by the boundary ideal. -/
def imageCycle :
    NodalCycleNumbering (Empty.elim : Empty → (D[P].subscheme ↘ S).smoothLocus) n :=
  letI : PrestableFamily (P.boundary ↘ S) := P.prestable
  (boundaryImageIso P).mapNodalCycleNumbering P.cycle

/-- Transport to the boundary subscheme preserves the numbered branches. -/
theorem boundaryCycleAction_boundaryImageIso :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    (boundaryImageIso P).boundaryCycleAction P.cycle (imageCycle P) = 1 := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  refine ((boundaryImageIso P).existsUnique_boundaryCycleAction P.cycle
    (D := imageCycle P)).unique (Iso.branch_boundaryCycleAction _ _ _) ?_
  intro j l
  simpa only [map_one, Equiv.Perm.one_apply, imageCycle] using
    ((boundaryImageIso P).branch_mapNodalCycleNumbering P.cycle j l)

/-- The transported component has the same generic point in the ambient surface. -/
theorem imageCycle_genericPoint (j : ZMod n) :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    D[P].subschemeι ((imageCycle P).componentGenericPoint j) =
      P.pair.hom.left (P.cycle.componentGenericPoint j) := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  have h := (boundaryImageIso P).apply_componentGenericPoint P.cycle (imageCycle P) j
  rw [boundaryCycleAction_boundaryImageIso, map_one, Equiv.Perm.one_apply] at h
  rw [← h, ← Scheme.Hom.comp_apply, boundaryImageIso_hom_comp]

/-- Every ambient boundary prime is the generic point of a numbered component. -/
theorem numberedBoundaryPrimes_surjective (hP : D[P].IsEffectiveCartier) :
    Function.Surjective (P.numberedBoundaryPrimes hP) := by
  intro x
  let p := D[P].boundaryPrimeEmbedding x
  have hp : (p : P.surface) ∈ D[P].support := by
    simpa only [p, coe_boundaryPrimeEmbedding] using (mem_boundaryPrimes.mp x.property).1
  obtain ⟨v, hv⟩ := hP.exists_subschemeι_blowupComponentGeneric_eq (k := k) hp
  obtain ⟨j, hj⟩ := (P.imageCycle).component.surjective v
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  refine ⟨j, Subtype.ext ?_⟩
  rw [← hj, ← NodalCycleNumbering.componentGenericPoint_def, P.imageCycle_genericPoint] at hv
  simpa only [numberedBoundaryPrimes_apply_val, coe_boundaryPrime, p, coe_boundaryPrimeEmbedding]
    using hv

variable {P} {Q : MarkedSurface k n B₁ X₁}

/-- A marked pair isomorphism induces an isomorphism of the subschemes cut out by the
boundary ideals. -/
def imagePairIso (e : P.pair ≅ Q.pair) : D[P].subscheme ≅ D[Q].subscheme :=
  (boundaryImageIso P).symm ≪≫ (boundaryIso e ≪≫ boundaryImageIso Q)

instance (e : P.pair ≅ Q.pair) : (imagePairIso e).hom.IsOver S :=
  inferInstanceAs (((boundaryImageIso P).inv ≫ (boundaryIso e).hom ≫
    (boundaryImageIso Q).hom).IsOver S)

/-- The induced isomorphism commutes with the inclusions into the ambient surfaces. -/
theorem imagePairIso_hom_comp (e : P.pair ≅ Q.pair) :
    (imagePairIso e).hom ≫ D[Q].subschemeι = D[P].subschemeι ≫ (surfaceIso e).hom := by
  apply (cancel_epi (boundaryImageIso P).hom).mp
  simpa only [imagePairIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    boundaryImageIso_hom_comp_assoc, boundaryImageIso_hom_comp] using
      MarkedSurface.boundaryIso_hom_comp e

/-- Transport to the image subschemes preserves the entire action on the numbered branches. -/
theorem imagePairIso_boundaryAction (e : P.pair ≅ Q.pair) :
    letI : PrestableFamily (P.boundary ↘ S) := P.prestable
    letI : PrestableFamily (Q.boundary ↘ S) := Q.prestable
    (imagePairIso e).boundaryCycleAction (imageCycle P) (imageCycle Q) =
      (boundaryIso e).boundaryCycleAction P.cycle Q.cycle := by
  let : PrestableFamily (P.boundary ↘ S) := P.prestable
  let : PrestableFamily (Q.boundary ↘ S) := Q.prestable
  let : (boundaryImageIso P).symm.hom.IsOver S :=
    inferInstanceAs ((boundaryImageIso P).inv.IsOver S)
  let : (boundaryIso e ≪≫ boundaryImageIso Q).hom.IsOver S :=
    inferInstanceAs (((boundaryIso e).hom ≫ (boundaryImageIso Q).hom).IsOver S)
  calc
    _ = (boundaryIso e ≪≫ boundaryImageIso Q).boundaryCycleAction P.cycle (imageCycle Q) *
          (boundaryImageIso P).symm.boundaryCycleAction (imageCycle P) P.cycle :=
      Iso.boundaryCycleAction_trans _ _ _ _ _
    _ = _ := by
      have hinv := (boundaryImageIso P).boundaryCycleAction_symm P.cycle (imageCycle P)
      rw [boundaryCycleAction_boundaryImageIso, inv_one] at hinv
      rw [Iso.boundaryCycleAction_trans (boundaryIso e) P.cycle Q.cycle, hinv,
        boundaryCycleAction_boundaryImageIso, one_mul, mul_one]

/-- The numbering enumerates exactly the prime divisors supported on the boundary. -/
theorem mem_range_boundaryPrime_iff (P : MarkedSurface k n B₀ X₀)
    (hD : D[P].IsEffectiveCartier) (x : CodimensionOnePoint P.surface) :
    x ∈ Set.range (P.boundaryPrime hD) ↔ (x : P.surface) ∈ D[P].support := by
  constructor
  · rintro ⟨j, rfl⟩
    exact (mem_boundaryPrimes.mp (P.boundaryPrime_mem_boundaryPrimes hD j)).1
  · intro hx
    obtain ⟨v, hv⟩ := hD.exists_range_blowupComponent_comp_subschemeι (k := k) hx
    obtain ⟨j, rfl⟩ := P.imageCycle.component.surjective v
    have hr := (D[P]).subscheme.range_blowupComponent_comp
      (P.imageCycle.component j) D[P].subschemeι D[P].subschemeι.isClosedMap
    rw [← P.imageCycle.componentGenericPoint_def, P.imageCycle_genericPoint j,
      ← P.coe_boundaryPrime hD j, hv] at hr
    refine ⟨j, CodimensionOnePoint.eq_of_specializes ?_⟩
    rw [specializes_iff_mem_closure, ← hr]
    exact subset_closure (Set.mem_singleton _)

/-- The Picard marking identifies the orthogonal to the numbered boundary classes with
the geometric boundary orthogonal. -/
theorem picardMarking_mem_boundaryOrthogonal_iff (P : MarkedSurface k n B₀ X₀)
    (hD : D[P].IsEffectiveCartier) (x : L₀) :
    letI : P.surface.IsProjectiveOver k := P.projective
    letI : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
    P.picardMarking x ∈ D[P].boundaryOrthogonal k ↔
      x ∈ B₀.orthogonal (Submodule.span ℤ (Set.range (P.boundaryClass hD))) := by
  let : P.surface.IsProjectiveOver k := P.projective
  let : SmoothOfRelativeDimension 2 (P.surface ↘ S) := P.smooth
  let := (P.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let U : P.surface.Opens := D[P].support.compl
  have hU (p : CodimensionOnePoint P.surface) :
      (p : P.surface) ∉ U ↔ p ∈ Set.range (P.boundaryPrime hD) :=
    not_not.trans (P.mem_range_boundaryPrime_iff hD p).symm
  rw [IdealSheafData.boundaryOrthogonal_def D[P] k]
  rw [U.primeDivisorSpanCompl_eq_span_of_mem_iff _ hU]
  simp only [LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin_span,
    Set.forall_mem_range, ← P.picardMarking_boundaryClass hD, P.intersectionBilinForm_picardMarking]

end BoundaryImage

end MarkedSurface

namespace FiberRealization

variable [IsIntegral X₀] [X₀.IsSeparated] [X₁.IsSeparated]
  {F : X₀ ⤏ X₁} {I : B₁.IsometryEquiv B₀} {g : DihedralGroup n}

/-- Picard pullback along a fiber realization sends a numbered boundary class to the
class at the inverse image of its component under the forward dihedral action. -/
theorem picard_boundaryClass (R : FiberRealization M N F I g)
    (hM : M.pair.hom.left.ker.IsEffectiveCartier) (hN : N.pair.hom.left.ker.IsEffectiveCartier)
    (j : ZMod n) :
    I (N.boundaryClass hN j) = M.boundaryClass hM (cycleVertexPerm g⁻¹ j) := by
  let : PrestableFamily (M.boundary ↘ S) := M.prestable
  let : PrestableFamily (N.boundary ↘ S) := N.prestable
  let : SmoothOfRelativeDimension 2 (M.surface ↘ S) := M.smooth
  let : SmoothOfRelativeDimension 2 (N.surface ↘ S) := N.smooth
  let := (M.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let := (N.surface ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  have hprime := M.map_boundaryPrime hM hN R.iso (cycleVertexPerm g⁻¹ j)
  rw [R.boundaryAction_eq, ← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Equiv.Perm.one_apply] at hprime
  apply M.picardMarking.injective
  rw [R.picard_eq, N.picardMarking_boundaryClass, M.picardMarking_boundaryClass, toMul_ofMul]
  exact congrArg Additive.ofMul (hprime ▸
    LineBundleClass.pullback_primeDivisorClass_mapOfIsOpenImmersion
      (MarkedSurface.surfaceIso R.iso).hom (M.boundaryPrime hM (cycleVertexPerm g⁻¹ j)))

end FiberRealization

namespace GeometricRealization

variable [IsIntegral X₀] [X₀.IsSeparated] [X₁.IsSeparated]
  {T₀ T₁ : Over (Spec (CommRingCat.of k))}
  [Nonempty T₀.left] [Smooth T₀.hom]
  {P₀ : Point T₀ → MarkedSurface k n B₀ X₀} {P₁ : Point T₁ → MarkedSurface k n B₁ X₁}
  {C : T₀.left.PartialMap T₁.left} [IsDominant C.hom] [C.IsOver T₀.hom T₁.hom]
  {F : X₀ ⤏ X₁} [F.IsDominant] (R : GeometricRealization P₀ P₁ C F)

/-- The constant Picard pullback takes the target boundary classes to the source classes
indexed by the inverse dihedral action. The classes can be read at any center in the domain. -/
theorem picard_boundaryClass (c : CenterPoint C)
    (h₀ : (P₀ (c ≫ C.domainSource)).pair.hom.left.ker.IsEffectiveCartier)
    (h₁ : (P₁ (c ≫ C.domainTarget)).pair.hom.left.ker.IsEffectiveCartier)
    (j : ZMod n) :
    R.picard ((P₁ (c ≫ C.domainTarget)).boundaryClass h₁ j) =
      (P₀ (c ≫ C.domainSource)).boundaryClass h₀ (cycleVertexPerm R.boundaryAction⁻¹ j) :=
  (R.fiber c).picard_boundaryClass h₀ h₁ j

variable {P : Point T₀ → MarkedSurface k n B₀ X₀}
  {C₀ : T₀.left.PartialMap T₀.left} [IsDominant C₀.hom] [C₀.IsOver T₀.hom T₀.hom]
  {F₀ : X₀ ⤏ X₀} [F₀.IsDominant] (A : GeometricRealization P P C₀ F₀)
  (D : ZMod n → L₀) (hD : ∀ c, (P c).pair.hom.left.ker.IsEffectiveCartier)
  (hmark : ∀ c j, (P c).boundaryClass (hD c) j = D j)

include hmark in
/-- For a fixed marked boundary, the Picard pullback together with the branch orientation
of a geometric self-realization belongs to the signed boundary isometry group. -/
theorem picard_mem_signedBoundaryIsometryGroup :
    (B₀.isometryGroupEquivIsometryEquiv.symm A.picard, A.orientation) ∈
      signedBoundaryIsometryGroup B₀ D := by
  obtain ⟨c⟩ := nonempty_centerPoint C₀
  refine (mem_signedBoundaryIsometryGroup_iff B₀ D).2
    ⟨cycleVertexPerm A.boundaryAction⁻¹ 0, fun j ↦ ?_⟩
  have h := A.picard_boundaryClass c (hD _) (hD _) j
  rw [hmark, hmark, cycleVertexPerm_apply, map_inv, Int.units_inv_eq_self] at h
  simpa only [LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm, orientation_def,
    Units.smul_def] using h

include hmark in
/-- An orientation-preserving geometric self-realization of a fixed marked boundary
acts by a boundary rotation on the Picard lattice. -/
theorem picard_mem_boundaryRotationGroup (hpos : A.orientation = 1) :
    B₀.isometryGroupEquivIsometryEquiv.symm A.picard ∈ boundaryRotationGroup B₀ D := by
  have h := A.picard_mem_signedBoundaryIsometryGroup D hD hmark
  rw [hpos] at h
  simpa only [mem_boundaryRotationGroup_iff, mem_signedBoundaryIsometryGroup_iff, one_smul] using h

include hmark in
/-- The signed Picard action of a geometric self-realization in a fixed boundary marking. -/
def toSignedBoundaryIsometry : signedBoundaryIsometryGroup B₀ D :=
  ⟨(B₀.isometryGroupEquivIsometryEquiv.symm A.picard, A.orientation),
    A.picard_mem_signedBoundaryIsometryGroup D hD hmark⟩

@[simp]
theorem coe_toSignedBoundaryIsometry :
    (↑(A.toSignedBoundaryIsometry D hD hmark) : B₀.isometryGroup × ℤˣ) =
      (B₀.isometryGroupEquivIsometryEquiv.symm A.picard, A.orientation) :=
  (rfl)

include hmark in
@[simp]
theorem toSignedBoundaryIsometry_refl :
    (GeometricRealization.refl P).toSignedBoundaryIsometry D hD hmark = 1 := by
  apply Subtype.ext
  rw [coe_toSignedBoundaryIsometry, Subgroup.coe_one]
  refine Prod.ext ?_ ?_
  · apply Subtype.ext
    refine LinearEquiv.ext fun a ↦ ?_
    simp only [refl_picard, LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm]
    rfl
  · simp [orientation_def]

variable [PreirreducibleSpace T₀.left]
  {C₁ : T₀.left.PartialMap T₀.left} [IsDominant C₁.hom] [C₁.IsOver T₀.hom T₀.hom]
  {F₁ : X₀ ⤏ X₀} [F₁.IsDominant]

include hmark in
/-- Signed Picard actions compose by pullback, with the first geometric map's action
on the left of the product. -/
@[simp]
theorem toSignedBoundaryIsometry_comp (A' : GeometricRealization P P C₁ F₁) :
    (A.comp A').toSignedBoundaryIsometry D hD hmark =
      A.toSignedBoundaryIsometry D hD hmark * A'.toSignedBoundaryIsometry D hD hmark := by
  apply Subtype.ext
  simp only [coe_toSignedBoundaryIsometry, Subgroup.coe_mul, Prod.mk_mul_mk]
  refine Prod.ext ?_ ((A.comp_orientation A').trans (mul_comm _ _))
  apply Subtype.ext
  refine LinearEquiv.ext fun a ↦ ?_
  simp only [comp_picard, Subgroup.coe_mul, mul_apply_eq_comp,
    LinearMap.BilinForm.coe_isometryGroupEquivIsometryEquiv_symm]
  rfl

end GeometricRealization

end QPainleve.SignedClusterModularGroup
