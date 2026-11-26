/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.GroupTheory.GroupExtension.Basic
public import QPainleve.AlgebraicGeometry.Curves.DualGraph.Cycle.Action
public import QPainleve.SignedClusterModularGroup.BoundaryReflection
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.GroupTheory.GroupExtension.Splitting

/-!
# Signed boundary isometries

A signed boundary isometry of a cyclic family `D` is an isometry together with a sign
`ε : ℤˣ` such that its action on the family is `D j ↦ D (ε • j + k)` for some shift `k`.
The positive-sign kernel consists of rotations. A reversing involution splits the sign
extension, so Mathlib's `GroupExtension.Splitting.semidirectProductMulEquiv` gives the
semidirect product with conjugation by that involution.
For an injectively numbered boundary, `SignedBoundaryIsometryGroup.boundaryAction`
reads the forward dihedral action from Picard pullback and the branch sign.
For a unimodular symmetric cycle lattice with primitive characteristic total class,
`SignedBoundaryIsometryGroup.CycleReversingInvolution` records the signed element and
its action on the lattice. The same witness supplies the splitting and the action on
the boundary orthogonal complement.

For an injectively indexed family of length at least three, the underlying isometry determines
the sign. For lengths one and two, both signs give the same index action and the signed group
is a direct product with `ℤˣ`.
-/

public section

namespace QPainleve

variable {L : Type*} [AddCommGroup L] [Module ℤ L] {n : ℕ}
variable (B : LinearMap.BilinForm ℤ L) (D : ZMod n → L)

/-- The subgroup of isometry-sign pairs that act on the boundary by a signed shift. -/
def signedBoundaryIsometryGroup : Subgroup (B.isometryGroup × ℤˣ) where
  carrier := {p | ∃ k : ZMod n, ∀ j, p.1.val (D j) = D (p.2 • j + k)}
  one_mem' := ⟨0, fun j => by simp⟩
  mul_mem' := by
    rintro ⟨g, ε⟩ ⟨h, η⟩ ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨ε • l + k, fun j => ?_⟩
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, mul_apply_eq_comp]
    rw [hl, hk, smul_add, mul_smul, add_assoc]
  inv_mem' := by
    rintro ⟨g, ε⟩ ⟨k, hk⟩
    refine ⟨-(ε⁻¹ • k), fun j => ?_⟩
    -- Apply the forward isometry to compare the two potential inverse images.
    simp only [Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, LinearEquiv.coe_inv]
    apply g.val.injective
    rw [LinearEquiv.apply_symm_apply, hk]
    simp [smul_add, ← mul_smul]

/-- Membership in the signed group is the existence of a shift with the given sign. -/
theorem mem_signedBoundaryIsometryGroup_iff {p : B.isometryGroup × ℤˣ} :
    p ∈ signedBoundaryIsometryGroup B D ↔
      ∃ k : ZMod n, ∀ j, p.1.val (D j) = D (p.2 • j + k) :=
  Iff.rfl

/-- The subgroup of boundary isometries acting on the indices by a rotation. -/
def boundaryRotationGroup : Subgroup B.isometryGroup :=
  (signedBoundaryIsometryGroup B D).comap (MonoidHom.inl _ _)

/-- Membership in the rotation group is the existence of a constant boundary shift. -/
theorem mem_boundaryRotationGroup_iff {g : B.isometryGroup} :
    g ∈ boundaryRotationGroup B D ↔
      ∃ k : ZMod n, ∀ j : ZMod n, g.val (D j) = D (j + k) := by
  rw [boundaryRotationGroup, Subgroup.mem_comap, mem_signedBoundaryIsometryGroup_iff]
  simp

namespace SignedBoundaryIsometryGroup

open DihedralGroup MulOpposite

/-- Projection to the underlying isometry. -/
def toIsometry : signedBoundaryIsometryGroup B D →* B.isometryGroup :=
  (MonoidHom.fst _ _).domRestrict _

@[simp]
theorem toIsometry_apply (p : signedBoundaryIsometryGroup B D) :
    toIsometry B D p = p.val.1 := (rfl)

/-- A signed boundary isometry permutes the indexed boundary classes. -/
theorem exists_indexPerm (g : signedBoundaryIsometryGroup B D) :
    ∃ p : Equiv.Perm (ZMod n), ∀ i, (toIsometry B D g).val (D i) = D (p i) := by
  obtain ⟨k, hk⟩ := (mem_signedBoundaryIsometryGroup_iff B D).mp g.property
  refine ⟨(MulAction.toPerm g.val.2).trans (Equiv.addRight k), fun i ↦ ?_⟩
  simpa only [toIsometry_apply, Equiv.trans_apply, MulAction.toPerm_apply, Equiv.coe_addRight]
    using hk i

/-- The unsigned action of a signed boundary isometry fixes the total boundary class. -/
theorem toIsometry_apply_sum [NeZero n] (g : signedBoundaryIsometryGroup B D) :
    (toIsometry B D g).val (∑ i, D i) = ∑ i, D i := by
  obtain ⟨p, hp⟩ := exists_indexPerm B D g
  rw [map_sum]
  simpa only [hp] using Equiv.sum_comp p D

/-- Projection to the sign of the boundary action. -/
def sign : signedBoundaryIsometryGroup B D →* ℤˣ :=
  (MonoidHom.snd _ _).domRestrict _

@[simp]
theorem sign_apply (p : signedBoundaryIsometryGroup B D) :
    sign B D p = p.val.2 := (rfl)

/-- A signed boundary isometry acts by pullback along a dihedral action with its
specified branch sign. This uses the inverse of its permutation of the classes. -/
theorem exists_cycleAction_pullback (g : signedBoundaryIsometryGroup B D) :
    ∃ a : DihedralGroup n, DihedralGroup.cycleOrientationSign a = sign B D g ∧
      ∀ j, (toIsometry B D g).val (D (DihedralGroup.cycleVertexPerm a j)) = D j := by
  obtain ⟨k, hk⟩ := (mem_signedBoundaryIsometryGroup_iff B D).mp g.property
  rcases Int.units_eq_one_or (sign B D g) with h | h
  · refine ⟨DihedralGroup.r (-k), (DihedralGroup.cycleOrientationSign_r _).trans h.symm, ?_⟩
    intro j
    simpa only [toIsometry_apply, DihedralGroup.cycleVertexPerm_r_apply, ← sign_apply,
      h, one_smul, neg_add_cancel_right] using hk (j + -k)
  · refine ⟨DihedralGroup.sr (-k), (DihedralGroup.cycleOrientationSign_sr _).trans h.symm, ?_⟩
    intro j
    simpa only [toIsometry_apply, DihedralGroup.cycleVertexPerm_sr_apply, neg_neg, ← sign_apply,
      h, Units.neg_smul, one_smul, neg_sub, sub_add_cancel] using hk (k - j)

private theorem cycleAction_eq_of_pullback (hD : Function.Injective D)
    (g : signedBoundaryIsometryGroup B D) {a b : DihedralGroup n}
    (ha : cycleOrientationSign a = sign B D g ∧
      ∀ j, (toIsometry B D g).val (D (cycleVertexPerm a j)) = D j)
    (hb : cycleOrientationSign b = sign B D g ∧
      ∀ j, (toIsometry B D g).val (D (cycleVertexPerm b j)) = D j) : a = b :=
  eq_of_cycleVertexPerm_eq_of_cycleOrientationSign_eq
    (Equiv.ext fun j ↦ hD ((toIsometry B D g).val.injective ((ha.2 j).trans (hb.2 j).symm)))
    (ha.1.trans hb.1.symm)

/-- The forward dihedral action determined by Picard pullback on an injectively
numbered boundary and by the specified orientation sign. The opposite group
accounts for the reversal of composition under pullback. -/
noncomputable def boundaryAction (hD : Function.Injective D) :
    (signedBoundaryIsometryGroup B D)ᵐᵒᵖ →* DihedralGroup n where
  toFun g := (exists_cycleAction_pullback B D g.unop).choose
  map_one' := by
    refine cycleAction_eq_of_pullback B D hD _ (exists_cycleAction_pullback B D _).choose_spec
      ⟨?_, fun j ↦ ?_⟩ <;> simp
  map_mul' g h := by
    have hg := (exists_cycleAction_pullback B D g.unop).choose_spec
    have hh := (exists_cycleAction_pullback B D h.unop).choose_spec
    refine cycleAction_eq_of_pullback B D hD _ (exists_cycleAction_pullback B D _).choose_spec
      ⟨?_, fun j ↦ ?_⟩
    · rw [map_mul, hg.1, hh.1, unop_mul, map_mul, mul_comm]
    · rw [unop_mul, map_mul, Subgroup.coe_mul, mul_apply_eq_comp, map_mul, Equiv.Perm.mul_apply,
        hg.2, hh.2]

/-- The forward boundary action retains the sign, even when the vertex
permutation alone does not distinguish the two orientations. -/
@[simp]
theorem cycleOrientationSign_boundaryAction (hD : Function.Injective D)
    (g : signedBoundaryIsometryGroup B D) :
    cycleOrientationSign (boundaryAction B D hD (op g)) = sign B D g :=
  (exists_cycleAction_pullback B D g).choose_spec.1

/-- The class at the forward image of a component pulls back to that component's class. -/
@[simp↓] -- Simplify the pullback before unfolding `toIsometry`.
theorem toIsometry_apply_boundaryAction (hD : Function.Injective D)
    (g : signedBoundaryIsometryGroup B D) (j : ZMod n) :
    (toIsometry B D g).val (D (cycleVertexPerm (boundaryAction B D hD (op g)) j)) = D j :=
  (exists_cycleAction_pullback B D g).choose_spec.2 j

/-- A dihedral element gives the forward action exactly when its sign and
its pullback on boundary classes agree with the signed isometry. -/
theorem boundaryAction_eq_iff (hD : Function.Injective D)
    (g : signedBoundaryIsometryGroup B D) (a : DihedralGroup n) :
    boundaryAction B D hD (op g) = a ↔
      cycleOrientationSign a = sign B D g ∧
        ∀ j, (toIsometry B D g).val (D (cycleVertexPerm a j)) = D j := by
  have h := And.intro (cycleOrientationSign_boundaryAction B D hD g)
    (toIsometry_apply_boundaryAction B D hD g)
  exact ⟨fun e ↦ e ▸ h, cycleAction_eq_of_pullback B D hD g h⟩

/-- The forward image of a boundary index can be read by pulling back its class. -/
theorem cycleVertexPerm_boundaryAction_apply_eq_iff (hD : Function.Injective D)
    (g : signedBoundaryIsometryGroup B D) (j l : ZMod n) :
    cycleVertexPerm (boundaryAction B D hD (op g)) j = l ↔
      (toIsometry B D g).val (D l) = D j := by
  rw [← toIsometry_apply_boundaryAction B D hD g j, (toIsometry B D g).val.injective.eq_iff,
    hD.eq_iff, eq_comm]

/-- Include a boundary rotation with positive sign. -/
def rotationInclusion : boundaryRotationGroup B D →* signedBoundaryIsometryGroup B D :=
  (MonoidHom.inl B.isometryGroup ℤˣ).subgroupComap (signedBoundaryIsometryGroup B D)

@[simp]
theorem coe_rotationInclusion (g : boundaryRotationGroup B D) :
    ((rotationInclusion B D g : signedBoundaryIsometryGroup B D) : B.isometryGroup × ℤˣ) =
      (g.val, 1) := (rfl)

theorem rotationInclusion_injective : Function.Injective (rotationInclusion B D) :=
  (MonoidHom.inl B.isometryGroup ℤˣ).subgroupComap_injective (signedBoundaryIsometryGroup B D)
    fun _ _ h => congrArg Prod.fst h

/-- The positive-sign subgroup is the image of the rotations. -/
theorem range_rotationInclusion : (rotationInclusion B D).range = (sign B D).ker := by
  ext p
  rw [MonoidHom.mem_range, MonoidHom.mem_ker, sign_apply]
  constructor
  · rintro ⟨g, rfl⟩
    exact congrArg Prod.snd (coe_rotationInclusion B D g)
  · intro hp
    have hmem : p.val.1 ∈ boundaryRotationGroup B D := by
      have h := p.property
      rwa [← Prod.mk.eta (p := p.val), hp] at h
    refine ⟨⟨p.val.1, hmem⟩, Subtype.ext ?_⟩
    exact Prod.ext rfl hp.symm

variable {B D}

/-- A reversing isometry gives a signed group element with sign `-1`. -/
def reversal (g : B.IsometryEquiv B)
    (hg : ∃ k : ZMod n, ∀ j : ZMod n, g (D j) = D (-j + k)) :
    signedBoundaryIsometryGroup B D :=
  ⟨((B.isometryGroupEquivIsometryEquiv).symm g, -1),
    (mem_signedBoundaryIsometryGroup_iff B D).2 (by simpa [Units.smul_def] using hg)⟩

@[simp]
theorem coe_reversal (g : B.IsometryEquiv B)
    (hg : ∃ k : ZMod n, ∀ j : ZMod n, g (D j) = D (-j + k)) :
    ((reversal g hg : signedBoundaryIsometryGroup B D) : B.isometryGroup × ℤˣ) =
      (B.isometryGroupEquivIsometryEquiv.symm g, -1) := (rfl)

/-- The lift of a reversing involution squares to the identity in the signed group. -/
theorem reversal_mul_self (g : B.IsometryEquiv B)
    (hg : ∃ k : ZMod n, ∀ j : ZMod n, g (D j) = D (-j + k))
    (hinv : Function.Involutive g) : reversal g hg * reversal g hg = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, coe_reversal, Subgroup.coe_one]
  refine Prod.ext (Subtype.ext (LinearEquiv.ext fun x => ?_)) (by simp)
  simpa [Prod.fst_mul, mul_apply_eq_comp] using hinv x

variable (B D)

/-- A signed lift of the boundary reflection about a chosen component, together with
the square `-1` lattice class that meets that component once. -/
@[ext]
structure CycleReversingInvolution [NeZero n] where
  /-- The component at the cut. -/
  cut : ZMod n
  /-- The square `-1` lattice class at the cut. -/
  cutClass : L
  /-- The involution in the signed boundary isometry group. -/
  element : signedBoundaryIsometryGroup B D
  cutClass_sq : B cutClass cutClass = -1
  pairing_cutClass : ∀ j, B cutClass (D j) = if j = cut then 1 else 0
  sign_element : element.val.2 = -1
  element_mul_self : element * element = 1
  toIsometry_apply_cutClass : element.val.1.val cutClass = cutClass
  toIsometry_apply_boundary : ∀ j, element.val.1.val (D j) = D (2 * cut - j)
  toIsometry_apply_orthogonal : ∀ x ∈ B.orthogonal (Submodule.span ℤ (Set.range D)),
    element.val.1.val x = -x + (2 * B x cutClass) • (∑ j, D j)

attribute [simp] CycleReversingInvolution.cutClass_sq CycleReversingInvolution.sign_element
  CycleReversingInvolution.pairing_cutClass CycleReversingInvolution.element_mul_self
  CycleReversingInvolution.toIsometry_apply_cutClass
  CycleReversingInvolution.toIsometry_apply_boundary

/-- A unimodular symmetric cycle lattice with primitive characteristic total class
has a signed cycle-reversing involution. -/
theorem nonempty_cycleReversingInvolution [Module.Free ℤ L] [Module.Finite ℤ L] [NeZero n]
    [B.IsPerfPair] (hSymm : B.IsSymm)
    (hIntersection : ∀ i j : ZMod n,
      B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    (hPrimitive : TauCeti.IsPrimitive (∑ j, D j))
    (hCharacteristic : B.IsCharacteristic (∑ j, D j)) :
    Nonempty (CycleReversingInvolution B D) := by
  obtain ⟨j₀, f, g, hsq, hpair, hinv, hfix, _, hboundary, horthogonal⟩ :=
    exists_cycle_reversing_involution L B hSymm n D hIntersection hPrimitive hCharacteristic
  have hrev : ∃ k : ZMod n, ∀ j, g (D j) = D (-j + k) :=
    ⟨2 * j₀, fun j ↦ by simpa only [sub_eq_neg_add] using hboundary j⟩
  exact ⟨{
    cut := j₀
    cutClass := f
    element := reversal g hrev
    cutClass_sq := hsq
    pairing_cutClass := hpair
    sign_element := by simp
    element_mul_self := reversal_mul_self g hrev hinv
    toIsometry_apply_cutClass := by simpa using hfix
    toIsometry_apply_boundary := by simpa using hboundary
    toIsometry_apply_orthogonal := by simpa using horthogonal }⟩

/-- A negative-sign element ensures that the sign homomorphism is surjective. -/
theorem sign_surjective (s : signedBoundaryIsometryGroup B D) (hs : sign B D s = -1) :
    Function.Surjective (sign B D) := by
  intro ε
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact ⟨1, map_one _⟩
  · exact ⟨s, hs⟩

/-- A negative-sign element whose square is the identity has order two. -/
theorem orderOf_eq_two_of_sign_eq_neg_one (s : signedBoundaryIsometryGroup B D)
    (hs : sign B D s = -1) (hss : s * s = 1) : orderOf s = 2 := by
  refine orderOf_eq_prime (by rwa [pow_two]) ?_
  intro h
  simp [h] at hs

/-- The exact sequence of rotations, signed isometries, and signs. -/
def signExtension (hs : Function.Surjective (sign B D)) :
    GroupExtension (boundaryRotationGroup B D) (signedBoundaryIsometryGroup B D) ℤˣ where
  inl := rotationInclusion B D
  rightHom := sign B D
  inl_injective := rotationInclusion_injective B D
  range_inl_eq_ker_rightHom := range_rotationInclusion B D
  rightHom_surjective := hs

@[simp]
theorem signExtension_inl (hs : Function.Surjective (sign B D)) :
    (signExtension B D hs).inl = rotationInclusion B D := (rfl)

@[simp]
theorem signExtension_rightHom (hs : Function.Surjective (sign B D)) :
    (signExtension B D hs).rightHom = sign B D := (rfl)

/-- An involutive negative-sign element splits the sign extension, sending `-1` to that element. -/
def signSplitting (s : signedBoundaryIsometryGroup B D) (hs : sign B D s = -1)
    (hss : s * s = 1) : (signExtension B D (sign_surjective B D s hs)).Splitting where
  toFun ε := if ε = 1 then 1 else s
  map_one' := by simp
  map_mul' ε η := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;>
      rcases Int.units_eq_one_or η with rfl | rfl <;> simp [hss]
  rightInverse_rightHom ε := by
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [hs]

@[simp]
theorem signSplitting_neg_one (s : signedBoundaryIsometryGroup B D) (hs : sign B D s = -1)
    (hss : s * s = 1) : signSplitting B D s hs hss (-1) = s := by
  simp [signSplitting]

/-- In the semidirect product induced by the splitting, the negative sign acts on rotations
by conjugation by the underlying reversing involution. -/
theorem coe_signSplitting_conjAct_neg_one (s : signedBoundaryIsometryGroup B D)
    (hs : sign B D s = -1) (hss : s * s = 1) (g : boundaryRotationGroup B D) :
    ((signSplitting B D s hs hss).conjAct (-1) g).val =
      toIsometry B D s * g.val * toIsometry B D s := by
  have h := congrArg (toIsometry B D)
    (GroupExtension.inl_conjAct_comm (signExtension B D (sign_surjective B D s hs))
      (e := signSplitting B D s hs hss (-1)) (n := g))
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  simpa [GroupExtension.Splitting.conjAct, hinv] using h

/-- The reflection of a unimodular symmetric boundary cycle with primitive characteristic
total class gives an order-two section of the sign projection. The signed isometry group is
the corresponding semidirect product, with the negative sign acting by conjugation. -/
theorem exists_semidirectProductMulEquiv [Module.Free ℤ L] [Module.Finite ℤ L] [NeZero n]
    [B.IsPerfPair]
    (hSymm : B.IsSymm)
    (hIntersection : ∀ i j : ZMod n,
      B (D i) (D j) = (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0))
    (hPrimitive : TauCeti.IsPrimitive (∑ i : ZMod n, D i))
    (hCharacteristic : B.IsCharacteristic (∑ i : ZMod n, D i)) :
    ∃ (s : signedBoundaryIsometryGroup B D) (hs : sign B D s = -1) (hss : s * s = 1),
      (∃ j₀ : ZMod n, ∀ j, (toIsometry B D s).val (D j) = D (2 * j₀ - j)) ∧
      orderOf s = 2 ∧
      ∃ e : (boundaryRotationGroup B D ⋊[(signSplitting B D s hs hss).conjAct] ℤˣ) ≃*
          signedBoundaryIsometryGroup B D,
        e (SemidirectProduct.inr (-1)) = s := by
  obtain ⟨r⟩ := nonempty_cycleReversingInvolution B D hSymm hIntersection hPrimitive hCharacteristic
  have hsign : sign B D r.element = -1 := by simp
  let splitting := signSplitting B D r.element hsign r.element_mul_self
  refine ⟨r.element, hsign, r.element_mul_self, ⟨r.cut, fun j ↦ by simp⟩,
    orderOf_eq_two_of_sign_eq_neg_one B D r.element hsign r.element_mul_self,
    splitting.semidirectProductMulEquiv, ?_⟩
  rw [splitting.semidirectProductMulEquiv_inr]
  exact signSplitting_neg_one B D r.element hsign r.element_mul_self

/-- On an injectively indexed boundary of length at least three, the underlying isometry
determines the sign. -/
theorem toIsometry_injective (hn : 3 ≤ n) (hD : Function.Injective D) :
    Function.Injective (toIsometry B D) := by
  rw [injective_iff_map_eq_one]
  intro p hp
  rw [toIsometry_apply] at hp
  apply Subtype.ext
  refine Prod.ext hp ?_
  rcases Int.units_eq_one_or p.val.2 with hpos | hneg
  · exact hpos
  · exfalso
    obtain ⟨k, hk⟩ := (mem_signedBoundaryIsometryGroup_iff B D).1 p.property
    have heq (j : ZMod n) : j = -j + k :=
      hD (by simpa [hp, hneg, Units.smul_def] using hk j)
    have hk0 : k = 0 := by simpa using (heq 0).symm
    have htwo : (-1 : ZMod n) = 1 := by simpa [hk0] using (heq 1).symm
    rcases ZMod.neg_one_eq_one_iff.1 htwo with h | h <;> omega

/-- For boundary length one or two, both signs act identically on the indices. -/
theorem eq_prod_of_le_two [NeZero n] (hn : n ≤ 2) :
    signedBoundaryIsometryGroup B D = (boundaryRotationGroup B D).prod ⊤ := by
  have hneg : (-1 : ZMod n) = 1 := ZMod.neg_one_eq_one_iff.2 (by have := NeZero.ne n; omega)
  ext ⟨g, ε⟩
  have hε (j : ZMod n) : ε • j = j := by
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact one_smul _ _
    · rw [Units.smul_def, ← Int.cast_smul_eq_zsmul (ZMod n), Units.val_neg, Units.val_one,
        Int.cast_neg, Int.cast_one, hneg, one_smul]
  simp [mem_signedBoundaryIsometryGroup_iff, Subgroup.mem_prod, mem_boundaryRotationGroup_iff, hε]

/-- The signed group is a direct product for a boundary with one or two components. -/
def mulEquivProdOfLeTwo [NeZero n] (hn : n ≤ 2) :
    signedBoundaryIsometryGroup B D ≃* boundaryRotationGroup B D × ℤˣ :=
  (MulEquiv.subgroupCongr (eq_prod_of_le_two B D hn)).trans
    ((Subgroup.prodEquiv _ _).trans
      (MulEquiv.prodCongr (MulEquiv.refl _) Subgroup.topEquiv))

@[simp]
theorem coe_mulEquivProdOfLeTwo_symm_apply [NeZero n] (hn : n ≤ 2)
    (p : boundaryRotationGroup B D × ℤˣ) :
    ((mulEquivProdOfLeTwo B D hn).symm p).val = (p.1.val, p.2) := (rfl)

theorem coe_mulEquivProdOfLeTwo_apply [NeZero n] (hn : n ≤ 2)
    (p : signedBoundaryIsometryGroup B D) :
    let x := mulEquivProdOfLeTwo B D hn p
    (x.1.val, x.2) = p.val := by
  simpa using (coe_mulEquivProdOfLeTwo_symm_apply B D hn (mulEquivProdOfLeTwo B D hn p)).symm

/-- The pure sign change is the central element with underlying identity isometry for a
boundary with one or two components. -/
def centralSign [NeZero n] (hn : n ≤ 2) : signedBoundaryIsometryGroup B D :=
  (mulEquivProdOfLeTwo B D hn).symm (1, -1)

@[simp]
theorem coe_centralSign [NeZero n] (hn : n ≤ 2) :
    (centralSign B D hn).val = (1, -1) := by
  rw [centralSign, coe_mulEquivProdOfLeTwo_symm_apply]
  rfl

theorem centralSign_mem_center [NeZero n] (hn : n ≤ 2) :
    centralSign B D hn ∈ Subgroup.center (signedBoundaryIsometryGroup B D) := by
  rw [Subgroup.mem_center_iff]
  intro p
  apply Subtype.ext
  simp [coe_centralSign, Prod.mul_def, mul_comm p.val.2]

theorem orderOf_centralSign [NeZero n] (hn : n ≤ 2) : orderOf (centralSign B D hn) = 2 := by
  refine orderOf_eq_two_of_sign_eq_neg_one B D _ (by simp) (Subtype.ext ?_)
  simp [coe_centralSign, Prod.mul_def]

end SignedBoundaryIsometryGroup
end QPainleve
