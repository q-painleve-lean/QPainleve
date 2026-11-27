/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.ExchangeMatrix
public import QPainleve.Geometry.Toric.Fan.Picard.IntersectionMatrix
public import QPainleve.LinearAlgebra.Matrix.Kernel.Generator
public import QPainleve.SignedClusterModularGroup.Realization.Relations.Coordinates

import QPainleve.Algebra.Cluster.Word.LoopComparison.Reindex
import QPainleve.AlgebraicGeometry.Blowup.Tower.Nodal.IntersectionKernel
import QPainleve.AlgebraicGeometry.Chow.Isomorphism

/-!
# Signed loop comparison from the boundary intersection kernel

In an ordered toric model of a nef square-zero cycle, the primitive positive
kernel vector of the strict boundary intersection matrix records the multiplicities
of the total transform. The rays with multiplicity one survive the contraction.
This computes the numbered boundary order table from the cyclic ray coordinates
and the ray of each ordered internal center. The boundary comparison uses
`Fan.primeIntersectionMatrix_internalBlowupBoundaryPrime_eq` on the toric side and
`IsNodalBoundaryTower.intKernelGenerator_eq_totalTransform_and_surviving` on the nodal side.
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative Quiver
open QPainleve.BlowupTower QPainleve.CharacterTorus QPainleve.Cluster
open Scheme Scheme.IdealSheafData TauCeti TauCeti.AlgebraicGeometry TauCeti.Toric

namespace QPainleve.SignedClusterModularGroup

variable {k₀ : Type} [Field k₀] [IsAlgClosed k₀]

/-- The weight-one offsets of the integral kernel generator, with sign normalized at
offset zero. Return `none` unless the kernel has rank one and the filter has cardinality `n`. -/
def survivingRayOffsetsOfIntersectionMatrix {m n : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℤ) : Option (Set.powersetCard (Fin m) n) := do
  let weights ← A.intKernelGenerator 0
  let offsets := Finset.univ.filter (fun j ↦ weights j = 1)
  if h : offsets.card = n then some (Set.powersetCard.ofCard h) else none

/-- The offset filter returns the specified set exactly when a normalized kernel
generator exists and its weight-one entries are exactly that set. -/
theorem survivingRayOffsetsOfIntersectionMatrix_eq_some_iff {m n : ℕ} [NeZero m]
    (A : Matrix (Fin m) (Fin m) ℤ) (offsets : Set.powersetCard (Fin m) n) :
    survivingRayOffsetsOfIntersectionMatrix A = some offsets ↔
      ∃ weights, A.intKernelGenerator 0 = some weights ∧
        ∀ j, j ∈ offsets ↔ weights j = 1 := by
  unfold survivingRayOffsetsOfIntersectionMatrix
  cases A.intKernelGenerator 0 with
  | none => simp
  | some weights =>
    let selected := Finset.univ.filter (fun j ↦ weights j = 1)
    have hset : (∀ j, j ∈ offsets ↔ weights j = 1) ↔ selected = offsets.val := by
      rw [Finset.ext_iff]
      simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.powersetCard.mem_coe_iff]
      exact forall_congr' fun _ ↦ iff_comm
    simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, exists_eq_left', hset]
    split
    · rw [Option.some.injEq]
      exact Subtype.ext_iff
    · rename_i hc
      simp only [reduceCtorEq, false_iff]
      exact fun he ↦ hc ((congrArg Finset.card he).trans offsets.prop)

/-- The order table uses the rays whose computed total-transform weight is one.
The ray coordinates are in positive cyclic order starting at component zero.
The result is absent if the kernel or survivor count does not fit the input,
or if either generator list does not return to the computed exchange matrix. -/
def compareSignedLoopListsFromRays {m n r : ℕ} [NeZero m] [NeZero n]
    (ray : Fin m → Fin 2 → ℤ) (centerRay : Fin r → Fin m)
    (gs hs : List (Generator (Fin r))) : Option Bool := do
  let e := ZMod.finEquiv m
  let survivors : Set.powersetCard (Fin m) n ← survivingRayOffsetsOfIntersectionMatrix
    (internalBlowupBoundaryIntersectionMatrix (ray ∘ e.symm) (e ∘ centerRay))
  let charge := ray ∘ centerRay
  (SkewExchangeMatrix.ofChargeCoordinates charge).compareSignedLoopLists
    (boundaryOrderTable charge ray survivors) gs hs

/-- The ray comparison returns a result exactly when survivor selection succeeds
and the loop comparison for those survivors returns that result. -/
@[simp]
theorem compareSignedLoopListsFromRays_eq_some_iff {m n r : ℕ} [NeZero m] [NeZero n]
    (ray : Fin m → Fin 2 → ℤ) (centerRay : Fin r → Fin m)
    (gs hs : List (Generator (Fin r))) (result : Bool) :
    compareSignedLoopListsFromRays (n := n) ray centerRay gs hs = some result ↔
      ∃ survivors : Set.powersetCard (Fin m) n,
        survivingRayOffsetsOfIntersectionMatrix
          (internalBlowupBoundaryIntersectionMatrix (ray ∘ (ZMod.finEquiv m).symm)
            (ZMod.finEquiv m ∘ centerRay)) = some survivors ∧
        (SkewExchangeMatrix.ofChargeCoordinates (ray ∘ centerRay)).compareSignedLoopLists
          (boundaryOrderTable (ray ∘ centerRay) ray survivors) gs hs = some result := by
  simp only [compareSignedLoopListsFromRays, Option.bind_eq_bind, Option.bind_eq_some_iff]

/-- The ray comparison fails if survivor selection fails or the loop comparison
fails for the selected survivors. -/
@[simp]
theorem compareSignedLoopListsFromRays_eq_none_iff {m n r : ℕ} [NeZero m] [NeZero n]
    (ray : Fin m → Fin 2 → ℤ) (centerRay : Fin r → Fin m)
    (gs hs : List (Generator (Fin r))) :
    compareSignedLoopListsFromRays (n := n) ray centerRay gs hs = none ↔
      ∀ survivors : Set.powersetCard (Fin m) n,
        survivingRayOffsetsOfIntersectionMatrix
          (internalBlowupBoundaryIntersectionMatrix (ray ∘ (ZMod.finEquiv m).symm)
            (ZMod.finEquiv m ∘ centerRay)) = some survivors →
        (SkewExchangeMatrix.ofChargeCoordinates (ray ∘ centerRay)).compareSignedLoopLists
          (boundaryOrderTable (ray ∘ centerRay) ray survivors) gs hs = none := by
  simp only [compareSignedLoopListsFromRays, Option.bind_eq_bind, Option.bind_eq_none_iff]

/-- Renumbering the centers of a ray table preserves the whole comparison.
The intersection matrix counts the centers on each ray and the determinant
orders are permuted with the cluster coordinates. -/
theorem compareSignedLoopListsFromRays_reindex {m n r s : ℕ} [NeZero m] [NeZero n]
    (ray : Fin m → Fin 2 → ℤ) (centerRay : Fin r → Fin m) (e : Fin r ≃ Fin s)
    (gs hs : List (Generator (Fin r))) :
    compareSignedLoopListsFromRays (n := n) ray (centerRay ∘ e.symm)
        (gs.map (Generator.reindex e)) (hs.map (Generator.reindex e)) =
      compareSignedLoopListsFromRays (n := n) ray centerRay gs hs := by
  let p := ZMod.finEquiv m
  have hA : internalBlowupBoundaryIntersectionMatrix (ray ∘ p.symm) (p ∘ (centerRay ∘ e.symm)) =
      internalBlowupBoundaryIntersectionMatrix (ray ∘ p.symm) (p ∘ centerRay) := by
    have hcard (j : ZMod m) :
        (Finset.univ.filter fun k : Fin s ↦ p (centerRay (e.symm k)) = j).card =
          (Finset.univ.filter fun k : Fin r ↦ p (centerRay k) = j).card := by
      exact (Fintype.card_subtype _).symm.trans
        ((Fintype.card_congr
          (e.symm.subtypeEquivOfSubtype (p := fun k ↦ p (centerRay k) = j))).trans
          (Fintype.card_subtype _))
    ext a d
    simp only [internalBlowupBoundaryIntersectionMatrix_apply, Function.comp_apply, hcard]
  simp only [p] at hA
  let E := SkewExchangeMatrix.ofChargeCoordinates (ray ∘ centerRay)
  have hE : SkewExchangeMatrix.ofChargeCoordinates (ray ∘ (centerRay ∘ e.symm)) =
      (SkewExchangeMatrix.reindexPrefunctor e).obj E := by
    apply SkewExchangeMatrix.ext
    ext a d
    simp only [SkewExchangeMatrix.reindexPrefunctor_obj, SkewExchangeMatrix.reindex_matrix,
      Matrix.submatrix_apply, SkewExchangeMatrix.ofChargeCoordinates_matrix_apply,
      Function.comp_apply, E]
  have horders (t : Set.powersetCard (Fin m) n) :
      boundaryOrderTable (ray ∘ (centerRay ∘ e.symm)) ray t =
        fun j ↦ boundaryOrderTable (ray ∘ centerRay) ray t j ∘ e.symm := by
    funext j k
    simp only [boundaryOrderTable_apply, Function.comp_apply]
  apply Option.ext
  intro result
  simp only [compareSignedLoopListsFromRays_eq_some_iff, hA, hE, horders,
    SkewExchangeMatrix.compareSignedLoopLists_reindex, E]

namespace CompleteToricPresentation

open GeometricRealization (Point)

local notation "S" => Spec (CommRingCat.of k₀)
local notation "Centers[" r "]" => Over.mk (structureMap k₀ (Fin r → ℤ))
local notation "XTor[" r "]" => scheme k₀ (Fin r →₀ ℤ)
local notation "χ[" c "]" => pointsEquiv k₀ _ (Subtype.mk (Over.Hom.left c) (Over.w c))
local notation "D[" M "]" => Scheme.Hom.ker (Over.Hom.left (Arrow.hom (MarkedSurface.pair M)))
local notation "cartier[" M "]" => MarkedSurface.isEffectiveCartier_boundaryIdeal M
local notation "classOf(" h ")" => (LineBundleClass.mk (IsEffectiveCartier.toInvertibleSheaf h))⁻¹

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {b : Basis (Fin 2) ℤ N} {r n : ℕ} [NeZero n]
  {L γ : Type} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L}
  (Q : CompleteToricPresentation k₀ i b r L γ)
  {c₀ : Point (Over.mk (QPainleve.CharacterTorus.structureMap k₀ (Fin r →
    ℤ)))} {M₀ : MarkedSurface k₀ n B (QPainleve.CharacterTorus.scheme k₀ (Fin r →₀ ℤ))}

local instance instNonemptyIntersectionKernelCones : Nonempty Q.fan.cones :=
  Q.complete.nonempty_cones
local instance instNeZeroIntersectionKernelBoundaryLength : NeZero Q.length := Q.neZero
local instance instPrestableIntersectionKernelBoundary :
    PrestableFamily ((Q.fan.toricBoundaryIdeal k₀ Q.complete.nonempty_cones).subscheme ↘ S) :=
  Q.prestable

local notation "eFin" => ZMod.finEquiv Q.length
local notation "u" => Q.fan.rayEquivOfNodalCycleNumbering k₀ Q.regular (Q.cycle.rotate Q.origin)
local notation "rayAt" => Q.fan.rayFinEquivOfNodalCycleNumbering k₀ Q.regular Q.cycle Q.origin
local notation "fiber[" M "," c "]" =>
  ContractedToricFiber b Q.rays Q.regular Q.cycle Q.origin Q.inclusion χ[c] M

private theorem rotatedRayOrder_positive (j : ZMod Q.length) :
    b.detDualEquiv (u j).primitiveGenerator (u (j + 1)).primitiveGenerator = 1 ∧
      ∃ σ : Q.fan.cones, (u j).toCone ≤ σ ∧ (u (j + 1)).toCone ≤ σ := by
  rw [Fan.rayEquivOfNodalCycleNumbering_rotate_apply,
    Fan.rayEquivOfNodalCycleNumbering_rotate_apply, Q.rayEquivOfNodalCycleNumbering_eq_rayOrder]
  simpa only [add_right_comm j 1 Q.origin] using Q.positive (j + Q.origin)

local notation "center[" c "]" => (fun j : Fin r ↦ χ[c] (ofAdd (Pi.single j 1)))
local notation "Model[" c "]" => Fan.internalBlowupTower k₀ b Q.rays center[c]
local notation "J[" c "]" => Scheme.Hom.ker (WithBoundary.boundaryι (Sigma.snd Model[c]))
local notation "canonicalMatrix" => internalBlowupBoundaryIntersectionMatrix
  (fun j ↦ b.repr (Fan.Ray.primitiveGenerator (u j))) (Equiv.symm u ∘ Q.rays)

private theorem transportedBoundaryMatrix_eq {Y : Scheme} [Y.Over S] [IsIntegral Y]
    [IsNoetherian Y] [∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)]
    {E : Y.IdealSheafData} (e : (Model[c₀]).1 ≅ Y)
    (he : e.hom ≫ (Y ↘ S) = (WithBoundary.toTower (Model[c₀]).2).toBase ≫
      ((Q.fan.finiteFanScheme k₀) ↘ S))
    (hE : (E.comap e.hom).support = (J[c₀]).support) :
    Chow.primeIntersectionMatrix k₀ (fun j : Fin Q.length ↦ E.boundaryPrimeEmbedding
      (Fan.internalBlowupBoundaryPrimeEquivOfIso k₀ Q.regular b Q.rays center[c₀] e hE
        (u (eFin j)))) = canonicalMatrix := by
  let : (Model[c₀]).1.Over S := ⟨(WithBoundary.toTower (Model[c₀]).2).toBase ≫
    ((Q.fan.finiteFanScheme k₀) ↘ S)⟩
  let : e.hom.IsOver S := ⟨he⟩
  let : IsIntegral (Model[c₀]).1 :=
    Fan.isIntegral_internalBlowupTower k₀ b Q.rays center[c₀] Q.regular
  let : IsNoetherian (Model[c₀]).1 := (WithBoundary.toTower (Model[c₀]).2).isNoetherian
  let : SmoothOfRelativeDimension 2 ((Model[c₀]).1 ↘ S) :=
    Fan.smoothOfRelativeDimension_internalBlowupTower k₀ b Q.rays center[c₀] Q.regular
  let (y : (Model[c₀]).1) : UniqueFactorizationMonoid ((Model[c₀]).1.presheaf.stalk y) :=
    ((Model[c₀]).1 ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two y
  let p (j : Fin Q.length) := (J[c₀]).boundaryPrimeEmbedding
    (Fan.internalBlowupBoundaryPrimeEquiv k₀ Q.regular b Q.rays center[c₀] (u (eFin j)))
  have hp (j : Fin Q.length) : CodimensionOnePoint.mapOfIsOpenImmersion e.hom (p j) =
      E.boundaryPrimeEmbedding
        (Fan.internalBlowupBoundaryPrimeEquivOfIso k₀ Q.regular b Q.rays center[c₀] e hE
          (u (eFin j))) := by
    apply Subtype.ext
    simp [p, Fan.internalBlowupBoundaryPrimeEquivOfIso_apply_val]
  rw [← Fan.primeIntersectionMatrix_internalBlowupBoundaryPrime_eq k₀ b Q.regular Q.complete
    u Q.rays center[c₀] Q.rotatedRayOrder_positive]
  ext j k
  rw [Chow.primeIntersectionMatrix_apply, Chow.primeIntersectionMatrix_apply, ← hp, ← hp]
  symm
  simpa only [LineBundleClass.pullback_primeDivisorClass_mapOfIsOpenImmersion] using
    Chow.classIntersectionNumber_pullback_of_isIso k₀ e.hom
      (LineBundleClass.primeDivisorClass (CodimensionOnePoint.mapOfIsOpenImmersion e.hom (p j)))
      (LineBundleClass.primeDivisorClass (CodimensionOnePoint.mapOfIsOpenImmersion e.hom (p k)))

private theorem survivingRayOffsetsOfIntersectionMatrix_eq
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hnef : (classOf(cartier[M₀])).IsNef k₀ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0) :
    survivingRayOffsetsOfIntersectionMatrix canonicalMatrix =
      some (p₀.survivingBoundaryRayOffsets cartier[M₀]) := by
  obtain ⟨_, Y, T, hT, e, he⟩ := hnodal₀.exists_tower
  let E := (D[M₀]).comap T.toBase
  have hE : (E.comap e.inv).support = (J[c₀]).support := by
    dsimp only [E]
    rw [← comap_comp, he, p₀.support_comap]
  let enum := (eFin).toEquiv.trans ((u).trans
    (Fan.internalBlowupBoundaryPrimeEquivOfIso k₀ Q.regular b Q.rays center[c₀] e.symm hE))
  let : M₀.surface.IsProjectiveOver k₀ := M₀.projective
  let : SmoothOfRelativeDimension 2 (M₀.surface ↘ S) := M₀.smooth
  let : PrestableFamily (D[M₀].subscheme ↘ S) := M₀.prestable_boundaryImage
  let : ConnectedSpace D[M₀].subscheme :=
    GeometricallyConnected.connectedSpace_of_subsingleton (D[M₀].subscheme ↘ S)
  have hconn : _root_.IsConnected (D[M₀].support : Set M₀.surface) := by
    simpa only [range_subschemeι] using isConnected_range D[M₀].subschemeι.continuous
  let : IsNoetherian M₀.surface := isNoetherian_of_finiteType (M₀.surface ↘ S)
  let : Y.Over S := ⟨T.toBase ≫ (M₀.surface ↘ S)⟩
  let : IsIntegral Y := hT.isClosedPointTower.isIntegral (M₀.surface ↘ S)
  let : IsNoetherian Y := T.isNoetherian
  let : SmoothOfRelativeDimension 2 (Y ↘ S) :=
    hT.isClosedPointTower.smoothOfRelativeDimension (M₀.surface ↘ S)
  let (y : Y) : UniqueFactorizationMonoid (Y.presheaf.stalk y) :=
    (Y ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two y
  have hover : e.inv ≫ (Y ↘ S) = (WithBoundary.toTower (Model[c₀]).2).toBase ≫
      ((Q.fan.finiteFanScheme k₀) ↘ S) := by
    exact (Category.assoc _ _ _).symm.trans
      (((reassoc_of% he) (M₀.surface ↘ S)).trans p₀.projection_over)
  have hmatrix : Chow.primeIntersectionMatrix k₀ (E.boundaryPrimeEmbedding ∘ enum) =
      canonicalMatrix := Q.transportedBoundaryMatrix_eq e.symm hover hE
  have h := hT.intKernelGenerator_eq_totalTransform_and_surviving k₀
    cartier[M₀] M₀.boundaryIdeal_nodal hconn hnef hsq enum 0
  dsimp only at h
  obtain ⟨hkernel, hsurvives⟩ := h
  rw [hmatrix] at hkernel
  refine (survivingRayOffsetsOfIntersectionMatrix_eq_some_iff _ _).mpr ⟨_, hkernel, fun j ↦ ?_⟩
  rw [p₀.mem_survivingBoundaryRayOffsets, p₀.mem_range_numberedBoundaryRays_iff,
    Fan.rayFinEquivOfNodalCycleNumbering_apply]
  simpa only [Function.comp_apply, enum, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe,
    RingEquiv.coe_toEquiv, Fan.internalBlowupBoundaryPrimeEquivOfIso_apply_val, Iso.symm_hom,
    ← Scheme.Hom.comp_apply, he] using hsurvives j

/-- The weight-one offsets computed from the ordered toric ray coordinates are exactly
those of the numbered boundary of the nef square-zero pair. -/
theorem survivingRayOffsetsOfIntersectionMatrix_eq_some
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hnef : (classOf(cartier[M₀])).IsNef k₀ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    (ray : Fin Q.length → Fin 2 → ℤ) (centerRay : Fin r → Fin Q.length)
    (hray : ∀ j, ray j = b.repr (rayAt j).primitiveGenerator)
    (hcenter : ∀ j, rayAt (centerRay j) = Q.rays j) :
    survivingRayOffsetsOfIntersectionMatrix
        (internalBlowupBoundaryIntersectionMatrix (ray ∘ (eFin).symm) (eFin ∘ centerRay)) =
      some (p₀.survivingBoundaryRayOffsets cartier[M₀]) := by
  have hcoord : ray ∘ (eFin).symm = fun j k ↦ b.repr (u j).primitiveGenerator k := by
    funext j k
    simp only [Function.comp_apply, hray, Fan.rayFinEquivOfNodalCycleNumbering_apply,
      RingEquiv.apply_symm_apply]
  have hlabel : eFin ∘ centerRay = (u).symm ∘ Q.rays := by
    funext j
    simpa only [Function.comp_apply, Equiv.eq_symm_apply,
      ← Fan.rayFinEquivOfNodalCycleNumbering_apply] using hcenter j
  rw [hcoord, hlabel]
  exact Q.survivingRayOffsetsOfIntersectionMatrix_eq p₀ hnodal₀ hnef hsq

/-- With the ray coordinates of a nef square-zero nodal contraction, the executable
comparison uses exactly the seed and numbered order table of the reference fiber. -/
theorem compareSignedLoopListsFromRays_eq_compareSignedLoopLists
    (p₀ : fiber[M₀,c₀]) (hnodal₀ : p₀.IsNodalContraction)
    (hnef : (classOf(cartier[M₀])).IsNef k₀ (M₀.surface ↘ S))
    (hsq : Chow.classIntersectionNumber k₀ M₀.surface classOf(cartier[M₀])
      classOf(cartier[M₀]) = 0)
    (ray : Fin Q.length → Fin 2 → ℤ) (centerRay : Fin r → Fin Q.length)
    (hray : ∀ j, ray j = b.repr (rayAt j).primitiveGenerator)
    (hcenter : ∀ j, rayAt (centerRay j) = Q.rays j)
    (gs hs : List (Generator (Fin r))) :
    compareSignedLoopListsFromRays (n := n) ray centerRay gs hs =
      (Fan.rayExchangeMatrix b Q.rays).compareSignedLoopLists
        (p₀.numberedBoundaryOrders cartier[M₀]) gs hs := by
  have hsurvivors := Q.survivingRayOffsetsOfIntersectionMatrix_eq_some p₀ hnodal₀ hnef hsq
    ray centerRay hray hcenter
  have h := Q.isSignedLoopComparisonInput_of_rayCoordinates p₀ ray centerRay
    (p₀.survivingBoundaryRayOffsets cartier[M₀]) (fun j _ ↦ hray j) hcenter rfl
  have hE := SkewExchangeMatrix.ext (h.matrix_eq.trans (Fan.rayExchangeMatrix_matrix b Q.rays).symm)
  simp only [compareSignedLoopListsFromRays, hsurvivors, Option.bind_eq_bind, Option.bind_some,
    hE, h.orders_eq]

end CompleteToricPresentation

end QPainleve.SignedClusterModularGroup
