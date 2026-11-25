/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Birational
public import QPainleve.AlgebraicGeometry.Chow.Cremona
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime
public import QPainleve.SignedClusterModularGroup.Boundary.Intersection
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry

import Mathlib.Tactic.NormNum
import QPainleve.AlgebraicGeometry.CartierDivisor.Support
import QPainleve.AlgebraicGeometry.Chow.EffectiveClass
import QPainleve.AlgebraicGeometry.Chow.Nef.EffectiveTransport
import QPainleve.AlgebraicGeometry.Chow.NegativeCurve
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced

/-!
# Cremona isometries of anticanonical cycles

For a root-free nef square-zero anticanonical cycle, the Cremona isometry group is
the projection of the signed boundary isometry group to the Picard isometries.
Effectivity and negative self-intersection recover the boundary primes when there
are at least two components. The canonical class determines the single component
in the remaining case.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti TauCeti.AlgebraicGeometry
open LineBundleClass Scheme.IdealSheafData

universe u

namespace QPainleve.BoundaryCycle

variable {n : ℕ} [NeZero n]

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [Scheme.IsRationalOver (X ↘ Spec (.of k))]

local notation "B(" k ", " X ")" => Chow.intersectionBilinForm k X
local notation "K(" k ", " X ")" => mk (canonicalBundle k X 2)
local notation "I(" k ", " X ")" => Chow.classIntersectionNumber k X
local notation "P" => primeDivisorClass
local notation "δ(" k ", " X ")" => Additive.ofMul (K(k, X))⁻¹
local notation "Cr(" k ", " X ")" => Chow.cremonaIsometryGroup k X

section LocallyFactorial

variable [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]
  {D : X.IdealSheafData} [IsReduced D.subscheme] (hD : D.IsEffectiveCartier)
  (p : ZMod n ↪ CodimensionOnePoint X)
  (hp : ∀ r : CodimensionOnePoint X, (r : X) ∈ D.support ↔ r ∈ Set.range p)
  (hK : mk hD.toInvertibleSheaf = K(k, X))

local notation "A(" p ")" => (fun j ↦ Additive.ofMul (P (p j)))
local notation "G(" k ", " X ", " p ")" => signedBoundaryIsometryGroup B(k, X) A(p)
local notation "π(" k ", " X ", " p ")" => SignedBoundaryIsometryGroup.toIsometry B(k, X) A(p)

variable
  (hroot : ∀ r : CodimensionOnePoint X, Disjoint (closure {(r : X)}) D.support →
    I(k, X) (P r) (P r) ≠ -2)
  (hgram : ∀ i j : ZMod n, B(k, X) (A(p) i) (A(p) j) = (-2 : ℤ) * (if i = j then 1 else 0) +
    (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))

omit [IsAlgClosed k] [X.IsProjectiveOver k] [Scheme.IsRationalOver (X ↘ Spec (.of k))] in
include hD hp hK in
private theorem sum_boundaryClass_eq_anticanonical : ∑ j, A(p) j = δ(k, X) := by
  rw [← hD.ofMul_inv_toInvertibleSheaf_eq_sum_primeDivisorClass p hp, hK]

omit [IsReduced D.subscheme] in
include hD hp hK hroot hgram in
private theorem exists_perm_boundaryClass_of_mem_cremonaIsometryGroup
    {g : (B(k, X)).isometryGroup} (hg : g ∈ Cr(k, X)) (hn : 2 ≤ n) :
    ∃ σ : Equiv.Perm (ZMod n), ∀ j, g.val (A(p) j) = A(p) (σ j) := by
  let e := (B(k, X)).isometryGroupEquivIsometryEquiv g
  have he : ⇑e = ⇑g.val := (B(k, X)).coe_isometryGroupEquivIsometryEquiv g
  have hhom : e.toLinearEquiv.toAddMonoidHom = g.val.toAddMonoidHom :=
    AddMonoidHom.ext (congrFun he)
  have hmap := ((Chow.mem_cremonaIsometryGroup_iff k X).mp hg).2
  rw [← hhom] at hmap
  have hs (i : ZMod n) : I(k, X) (P (p i)) (P (p i)) = -2 := by
    simpa only [Chow.intersectionBilinForm_apply, toMul_ofMul] using
      diagonal_eq_neg_two_of_cycle_gram B(k, X) A(p) hgram hn i
  have hstep (i : ZMod n) : ∃ j, g.val (A(p) i) = A(p) j := by
    obtain ⟨r, ⟨hr, hrs⟩, _⟩ :=
      Chow.existsUnique_primeDivisorClass_eq_of_intersectionBilinForm_isometry k e hmap (p i)
        (by rw [hs]; norm_num)
    have hom := Chow.mem_boundary_of_primeDivisorClass_self_eq_neg_two k hD hK hroot r
      (hrs.trans (hs i))
    obtain ⟨j, rfl⟩ := (hp r).mp hom
    exact ⟨j, by simpa only [he] using hr.symm⟩
  choose f hf using hstep
  have hinj : Function.Injective f := fun i j hij ↦
    injective_of_cycle_gram B(k, X) A(p) hgram hn
      (g.val.injective ((hf i).trans (hij ▸ (hf j).symm)))
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hf⟩

include hD hp hK hroot hgram in
private theorem mem_range_of_mem_cremonaIsometryGroup {g : (B(k, X)).isometryGroup}
    (hg : g ∈ Cr(k, X)) : g ∈ (π(k, X, p)).range := by
  classical
  by_cases hn : 2 ≤ n
  · obtain ⟨σ, hσ⟩ := exists_perm_boundaryClass_of_mem_cremonaIsometryGroup k hD p hp hK
      hroot hgram hg hn
    have hpair (i j : ZMod n) : B(k, X) (A(p) (σ i)) (A(p) (σ j)) = B(k, X) (A(p) i) (A(p) j) := by
      rw [← hσ i, ← hσ j]
      exact LinearMap.BilinForm.mem_isometryGroup_iff.mp g.property _ _
    obtain ⟨η, a, ha⟩ := exists_signedShift_of_preserves_cycle_gram B(k, X) A(p) hgram σ hpair hn
    exact ⟨⟨(g, η), (mem_signedBoundaryIsometryGroup_iff B(k, X) A(p)).mpr
      ⟨a, fun j ↦ (hσ j).trans (congrArg A(p) (ha j))⟩⟩, by simp⟩
  · have hn₁ : n = 1 := by have := NeZero.ne n; omega
    let : Subsingleton (ZMod n) := not_nontrivial_iff_subsingleton.mp
      (fun h ↦ ZMod.nontrivial_iff.mp h hn₁)
    let : Unique (ZMod n) := uniqueOfSubsingleton 0
    have hsum : Additive.ofMul (P (p 0)) = δ(k, X) := by
      rw [← sum_boundaryClass_eq_anticanonical k hD p hp hK, Fintype.sum_unique]
      exact congrArg A(p) (Subsingleton.elim _ _)
    have hgK := ((Chow.mem_cremonaIsometryGroup_iff k X).mp hg).1
    refine ⟨⟨(g, 1), (mem_signedBoundaryIsometryGroup_iff B(k, X) A(p)).mpr
      ⟨0, fun j ↦ ?_⟩⟩, by simp⟩
    simp only [Subsingleton.elim j 0, one_smul, add_zero]
    rw [hsum]
    exact (map_neg g.val (Additive.ofMul K(k, X))).trans (congrArg Neg.neg hgK)

include hD hp hK hroot in
private theorem mem_cremonaIsometryGroup_of_signed
    (hnef : (K(k, X))⁻¹.IsNef k (X ↘ Spec (.of k))) (hsq : I(k, X) (K(k, X))⁻¹ (K(k, X))⁻¹ = 0)
    (s : G(k, X, p)) : π(k, X, p) s ∈ Cr(k, X) := by
  classical
  obtain ⟨σ, hσ⟩ := SignedBoundaryIsometryGroup.exists_indexPerm B(k, X) A(p) s
  let q := σ.toEmbedding.trans p
  have hq (r : CodimensionOnePoint X) : (r : X) ∈ D.support ↔ r ∈ Set.range q := by
    rw [hp]
    rw [← EquivLike.range_comp p σ]
    rfl
  have hδ : (π(k, X, p) s).val δ(k, X) = δ(k, X) := by
    rw [← sum_boundaryClass_eq_anticanonical k hD p hp hK]
    exact SignedBoundaryIsometryGroup.toIsometry_apply_sum B(k, X) A(p) s
  have hcan : (π(k, X, p) s).val (Additive.ofMul K(k, X)) = Additive.ofMul K(k, X) :=
    neg_injective ((map_neg (π(k, X, p) s).val (Additive.ofMul K(k, X))).symm.trans hδ)
  refine (Chow.mem_cremonaIsometryGroup_iff k X).mpr ⟨hcan, ?_⟩
  let e := (B(k, X)).isometryGroupEquivIsometryEquiv (π(k, X, p) s)
  have he : ⇑e = ⇑(π(k, X, p) s).val := (B(k, X)).coe_isometryGroupEquivIsometryEquiv (π(k, X, p) s)
  have hhom : e.toLinearEquiv.toAddMonoidHom = (π(k, X, p) s).val.toAddMonoidHom :=
    AddMonoidHom.ext (congrFun he)
  rw [← hhom]
  exact Chow.map_effectiveClasses_of_nef_anticanonical_isometry k hD hD p q hp hq hK hK
    hnef hnef hsq e (fun i ↦ by
      simpa only [he, q, Function.Embedding.trans_apply, Equiv.toEmbedding_apply] using hσ i)
    hroot hroot

end LocallyFactorial

/-- For a reduced nef square-zero anticanonical cycle with no internal `(-2)` curves,
the Cremona isometries are exactly the isometries underlying the signed boundary group.
The cycle Gram formula counts both incidences when the boundary has two components. -/
theorem range_toIsometry_eq_cremonaIsometryGroup_of_cycle_gram
    {D : X.IdealSheafData} [IsReduced D.subscheme]
    (hD : D.IsEffectiveCartier) (p : ZMod n ↪ CodimensionOnePoint X)
    (hp : ∀ r : CodimensionOnePoint X, (r : X) ∈ D.support ↔ r ∈ Set.range p)
    (hK : mk hD.toInvertibleSheaf = K(k, X)) (hnef : (K(k, X))⁻¹.IsNef k (X ↘ Spec (.of k)))
    (hsq : I(k, X) (K(k, X))⁻¹ (K(k, X))⁻¹ = 0) :
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    let := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let A := fun j ↦ Additive.ofMul (P (p j))
    (∀ i j : ZMod n, B(k, X) (A i) (A j) = (-2 : ℤ) * (if i = j then 1 else 0) +
      (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0)) →
    (∀ r : CodimensionOnePoint X, Disjoint (closure {(r : X)}) D.support →
      I(k, X) (P r) (P r) ≠ -2) →
    (SignedBoundaryIsometryGroup.toIsometry B(k, X) A).range = Cr(k, X) := by
  dsimp only
  intro hgram hroot
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  let := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    exact mem_cremonaIsometryGroup_of_signed k hD p hp hK hroot hnef hsq s
  · intro g hg
    exact mem_range_of_mem_cremonaIsometryGroup k hD p hp hK hroot hgram hg

/-- On a reduced nef square-zero anticanonical nodal cycle without internal `(-2)`
curves, the underlying signed boundary isometries are exactly the Cremona isometries.
The labels record both nodes of a two-component cycle separately. -/
theorem range_toIsometry_eq_cremonaIsometryGroup {D : X.IdealSheafData}
    (hD : D.IsEffectiveCartier)
    (hnodal : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of k)))
    (hK : mk hD.toInvertibleSheaf = K(k, X))
    (hnef : (K(k, X))⁻¹.IsNef k (X ↘ Spec (.of k)))
    (hsq : I(k, X) (K(k, X))⁻¹ (K(k, X))⁻¹ = 0)
    (p : ZMod n ↪ CodimensionOnePoint X) (node : ZMod n ↪ X)
    (hp : ∀ r : CodimensionOnePoint X, (r : X) ∈ D.support ↔ r ∈ Set.range p)
    (hinc : ∀ i j, i ≠ j →
      closure {(p i : X)} ∩ closure {(p j : X)} =
        node '' {e | (e = i ∧ j = i + 1) ∨ (e = j ∧ i = j + 1)}) :
    let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    let := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    (∀ r : CodimensionOnePoint X, Disjoint (closure {(r : X)}) D.support →
      I(k, X) (P r) (P r) ≠ -2) →
    (SignedBoundaryIsometryGroup.toIsometry B(k, X) (fun j ↦ Additive.ofMul (P (p j)))).range =
      Cr(k, X) := by
  dsimp only
  intro hroot
  let : IsReduced D.subscheme := hnodal.isReduced
  exact range_toIsometry_eq_cremonaIsometryGroup_of_cycle_gram k hD p hp hK hnef hsq
    (intersectionBilinForm_eq_of_nodal_cycle hD hnodal (hK.symm ▸ hnef)
      (hK.symm ▸ hsq) p node hp hinc) hroot

open SignedBoundaryIsometryGroup in
omit [Scheme.IsRationalOver (X ↘ Spec (.of k))] in
private theorem exists_cremonaProjection {d : ZMod n → Additive (LineBundleClass X)}
    (hrange : (toIsometry B(k, X) d).range = Cr(k, X))
    (hinj : 3 ≤ n → Function.Injective d) :
    ∃ π : signedBoundaryIsometryGroup B(k, X) d →* Cr(k, X),
      (∀ x, (π x).val = toIsometry B(k, X) d x) ∧ Function.Surjective π ∧
      (3 ≤ n → Function.Injective π) ∧
      (n ≤ 2 → ∃ e : boundaryRotationGroup B(k, X) d ≃* Cr(k, X),
        ∀ x, e x = π (rotationInclusion B(k, X) d x)) := by
  let f := toIsometry B(k, X) d
  let π := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp f.rangeRestrict
  have hπ (x : signedBoundaryIsometryGroup B(k, X) d) : (π x).val = f x := by
    simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.subgroupCongr_apply, MonoidHom.coe_rangeRestrict]
  have hsurj : Function.Surjective π :=
    (MulEquiv.subgroupCongr hrange).surjective.comp f.rangeRestrict_surjective
  refine ⟨π, hπ, hsurj, fun hn x y h ↦ ?_, fun hn ↦ ?_⟩
  · apply toIsometry_injective B(k, X) d hn (hinj hn)
    simpa only [hπ] using congrArg Subtype.val h
  · have hrot : boundaryRotationGroup B(k, X) d = Cr(k, X) := by
      rw [← hrange]
      ext g
      constructor
      · intro hg
        exact ⟨rotationInclusion B(k, X) d ⟨g, hg⟩, by
          simp only [toIsometry_apply, coe_rotationInclusion]⟩
      · rintro ⟨x, rfl⟩
        let y := mulEquivProdOfLeTwo B(k, X) d hn x
        have hy : y.1.val = x.val.1 :=
          congrArg Prod.fst (coe_mulEquivProdOfLeTwo_apply B(k, X) d hn x)
        rw [toIsometry_apply, ← hy]
        exact y.1.property
    refine ⟨MulEquiv.subgroupCongr hrot, fun x ↦ Subtype.ext ?_⟩
    rw [MulEquiv.subgroupCongr_apply, hπ, toIsometry_apply, coe_rotationInclusion]

open SignedBoundaryIsometryGroup in
/-- The signed boundary group of a numbered nef square-zero anticanonical cycle
without internal `(-2)` curves projects onto its Cremona isometries. The projection
is injective for at least three components and restricts to a rotation group
isomorphism for one or two components. -/
theorem exists_cremonaProjection_of_numbering
    {D : X.IdealSheafData} [PrestableFamily (D.subscheme ↘ Spec (.of k))]
    {ι : Type*} {marks : ι → (D.subscheme ↘ Spec (.of k)).smoothLocus}
    (A : Scheme.NodalCycleNumbering marks n)
    (hD : D.IsEffectiveCartier)
    (hK : mk hD.toInvertibleSheaf = K(k, X))
    (hnef : (mk hD.toInvertibleSheaf)⁻¹.IsNef k (X ↘ Spec (.of k)))
    (hsq : I(k, X) (mk hD.toInvertibleSheaf)⁻¹ (mk hD.toInvertibleSheaf)⁻¹ = 0) :
    letI : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
    letI := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
    let d := fun j ↦ Additive.ofMul (P (D.boundaryPrimeEmbedding (A.boundaryPrimeEquiv hD j)))
    (∀ p : CodimensionOnePoint X, Disjoint (closure {(p : X)}) D.support →
      I(k, X) (P p) (P p) ≠ -2) →
    ∃ π : signedBoundaryIsometryGroup B(k, X) d →* Cr(k, X),
      (∀ x, (π x).val = toIsometry B(k, X) d x) ∧ Function.Surjective π ∧
      (3 ≤ n → Function.Injective π) ∧
      (n ≤ 2 → ∃ e : boundaryRotationGroup B(k, X) d ≃* Cr(k, X),
        ∀ x, e x = π (rotationInclusion B(k, X) d x)) := by
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  let := (X ↘ Spec (.of k)).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  dsimp only
  intro hroot
  let p := (A.boundaryPrimeEquiv hD).toEmbedding.trans D.boundaryPrimeEmbedding
  have hp (q : CodimensionOnePoint X) : (q : X) ∈ D.support ↔ q ∈ Set.range p := by
    have hprimes : Set.range p = Set.range D.boundaryPrimeEmbedding :=
      (A.boundaryPrimeEquiv hD).surjective.range_comp _
    rw [hprimes, range_boundaryPrimeEmbedding]
    rfl
  have hN : AtWorstNodalOfRelativeDimensionOne (D.subscheme ↘ Spec (.of k)) :=
    PrestableFamily.atWorstNodalOfRelativeDimensionOne
  let : IsReduced D.subscheme := hN.isReduced
  have hgram := intersectionBilinForm_eq_of_nodal_cycle hD hN hnef hsq p
    ⟨A.ambientNode, A.ambientNode_injective⟩ hp
    (fun _ _ hij ↦ by
      simpa only [p, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
        coe_boundaryPrimeEmbedding, Function.Embedding.coeFn_mk] using
        A.closure_boundaryPrime_inter_of_ne hD hij)
  have hrange := range_toIsometry_eq_cremonaIsometryGroup_of_cycle_gram
    k hD p hp hK (hK ▸ hnef) (hK ▸ hsq) hgram hroot
  exact exists_cremonaProjection k hrange
    (fun hn ↦ injective_of_cycle_gram B(k, X) _ hgram (by omega))

end QPainleve.BoundaryCycle
