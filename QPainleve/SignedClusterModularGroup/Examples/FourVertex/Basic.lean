/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.SignedClusterModularGroup.Boundary.Restriction
import QPainleve.SignedClusterModularGroup.BoundaryCycle
import QPainleve.SignedClusterModularGroup.Faithfulness

/-!
# The Picard restriction kernel for the four-vertex seed

The marking is ordered by the two ruling classes, the four total exceptional
classes of the corner blowups, and the four exceptional classes of the
internal blowups. In these integral coordinates the only boundary rotations
that fix the orthogonal lattice pointwise are the identity and the half-turn.
The computation uses an integral multiple of a difference of two total
exceptional classes to rule out the other shifts.
-/

public section

open LinearMap Module Submodule
open scoped RightActions

namespace QPainleve.FourVertex

local notation "L" => Fin 10 → ℤ

/-- The intersection form in the basis `H₁,H₂,E₁,…,E₄,F₁,…,F₄` of total transforms. -/
def intersectionForm : LinearMap.BilinForm ℤ L :=
  BilinForm.linMulLin (.proj 0) (.proj 1) + BilinForm.linMulLin (.proj 1) (.proj 0) -
    ∑ i : Fin 8, BilinForm.linMulLin (.proj (i.natAdd 2)) (.proj (i.natAdd 2))

/-- The ruling classes pair with one another and the exceptional classes have square minus one. -/
theorem intersectionForm_apply (x y : L) :
    intersectionForm x y =
      x 0 * y 1 + x 1 * y 0 - ∑ i : Fin 8, x (i.natAdd 2) * y (i.natAdd 2) := by
  simp [intersectionForm]

/-- The intersection form in the total-transform basis is symmetric. -/
theorem intersectionForm_isSymm : intersectionForm.IsSymm :=
  ⟨fun x y ↦ by simp [intersectionForm_apply, mul_comm, add_comm]⟩

/-- The intersection form in the total-transform basis is nondegenerate. -/
theorem intersectionForm_nondegenerate : intersectionForm.Nondegenerate := by
  have h : intersectionForm.SeparatingLeft := by
    intro x hx
    ext i
    have hi := hx (Pi.single (Equiv.swap 0 1 i) 1)
    fin_cases i <;>
      simpa [intersectionForm_apply, Pi.single_apply, Fin.sum_univ_succ, Equiv.swap_apply_def]
        using hi
  exact ⟨h, fun x hx ↦ h x fun y ↦ (intersectionForm_isSymm.eq x y).trans (hx y)⟩

/-- The strict boundary classes in cyclic order, starting with `H₁ - E₁ - E₄`. -/
@[expose]
def boundaryClass (j : ZMod 8) : L :=
  ![![1, 0, -1, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, -1, 0, 0, 0],
    ![0, 1, -1, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, -1, 0, 0],
    ![1, 0, 0, -1, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, -1, 0],
    ![0, 1, 0, 0, -1, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0, 0, -1]]
      ((ZMod.finEquiv 8).symm j)

/-- Each boundary has square minus two and pairs to one with its two neighbors. -/
theorem intersectionForm_boundaryClass (i j : ZMod 8) :
    intersectionForm (boundaryClass i) (boundaryClass j) =
      (-2 : ℤ) * (if i = j then 1 else 0) +
        (if j = i + 1 then 1 else 0) + (if j = i - 1 then 1 else 0) := by
  revert i j
  decide

local notation "K" => intersectionForm.orthogonal (span ℤ (Set.range boundaryClass))

private def orthogonalGenerator (j : Fin 2) : L :=
  ![![1, 1, -1, 0, -1, 0, -1, 0, -1, 0], ![1, 1, 0, -1, 0, -1, 0, -1, 0, -1]] j

private theorem orthogonalGenerator_mem (j : Fin 2) : orthogonalGenerator j ∈ K := by
  refine Submodule.mem_orthogonalBilin_span.mpr ?_
  rintro _ ⟨i, rfl⟩
  revert i j
  decide

private theorem eq_smul_orthogonalGenerator {x : L} (hx : x ∈ K) :
    x = (-x 2) • orthogonalGenerator 0 + (-x 3) • orthogonalGenerator 1 := by
  have h (i : Fin 8) := Submodule.mem_orthogonalBilin_span.mp hx
    (Set.mem_range_self (ZMod.finEquiv 8 i))
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have h₃ := h 3
  have h₄ := h 4
  have h₅ := h 5
  have h₆ := h 6
  have h₇ := h 7
  simp [intersectionForm_apply, boundaryClass, Fin.sum_univ_succ] at h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  ext i
  fin_cases i <;> simp [orthogonalGenerator] <;> omega

private def boundaryOrthogonalCoordinates : K ≃ₗ[ℤ] Fin 2 → ℤ where
  toFun x := ![-x.val 2, -x.val 3]
  invFun c := c 0 • (⟨orthogonalGenerator 0, orthogonalGenerator_mem 0⟩ : K) +
    c 1 • (⟨orthogonalGenerator 1, orthogonalGenerator_mem 1⟩ : K)
  left_inv x := Subtype.ext (eq_smul_orthogonalGenerator x.property).symm
  right_inv c := by
    ext i
    fin_cases i <;> simp [orthogonalGenerator]
  map_add' x y := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [mul_neg]

/-- The orthogonal basis consists of the two classes supported on alternating exceptional pairs. -/
noncomputable def boundaryOrthogonalBasis : Basis (Fin 2) ℤ K :=
  Basis.ofEquivFun boundaryOrthogonalCoordinates

/-- Orthogonal basis coefficients are the negatives of the first two corner coefficients. -/
@[simp] theorem boundaryOrthogonalBasis_repr (x : K) (j : Fin 2) :
    boundaryOrthogonalBasis.repr x j = ![-x.val 2, -x.val 3] j := by
  rw [boundaryOrthogonalBasis, Basis.ofEquivFun_repr_apply]
  rfl

private theorem coe_boundaryOrthogonalBasis (j : Fin 2) :
    (boundaryOrthogonalBasis j : L) = orthogonalGenerator j := by
  rw [boundaryOrthogonalBasis, Basis.coe_ofEquivFun]
  fin_cases j <;> simp [boundaryOrthogonalCoordinates]

/-- The first basis vector subtracts the total exceptional classes of the first and
third corners and of the internal blowups on those rays from the sum of the rulings. -/
@[simp] theorem coe_boundaryOrthogonalBasis_zero :
    (boundaryOrthogonalBasis 0 : L) = ![1, 1, -1, 0, -1, 0, -1, 0, -1, 0] :=
  coe_boundaryOrthogonalBasis 0

/-- The second basis vector uses the second and fourth corners and internal blowups. -/
@[simp] theorem coe_boundaryOrthogonalBasis_one :
    (boundaryOrthogonalBasis 1 : L) = ![1, 1, 0, -1, 0, -1, 0, -1, 0, -1] :=
  coe_boundaryOrthogonalBasis 1

/-- The restricted pairing has negative affine `A₁` Gram matrix in the orthogonal basis. -/
theorem intersectionForm_boundaryOrthogonalBasis (i j : Fin 2) :
    intersectionForm (boundaryOrthogonalBasis i) (boundaryOrthogonalBasis j) =
      if i = j then -2 else 2 := by
  simp only [coe_boundaryOrthogonalBasis]
  revert i j
  decide

/-- The sum of the two basis vectors is the total boundary class. -/
theorem sum_boundaryOrthogonalBasis :
    ∑ j : Fin 2, (boundaryOrthogonalBasis j : L) = ∑ j : ZMod 8, boundaryClass j := by
  simp only [coe_boundaryOrthogonalBasis]
  ext i
  revert i
  decide

private def halfTurnPerm : Equiv.Perm (Fin 10) :=
  Equiv.swap 2 4 * Equiv.swap 3 5 * Equiv.swap 6 8 * Equiv.swap 7 9

private def halfTurnEquiv : L ≃ₗ[ℤ] L :=
  LinearEquiv.funCongrLeft ℤ ℤ halfTurnPerm

private theorem halfTurnEquiv_apply (x : L) :
    halfTurnEquiv x = ![x 0, x 1, x 4, x 5, x 2, x 3, x 8, x 9, x 6, x 7] := by
  ext i
  fin_cases i <;> rfl

private theorem halfTurnEquiv_isometry (x y : L) :
    intersectionForm (halfTurnEquiv x) (halfTurnEquiv y) = intersectionForm x y := by
  rw [intersectionForm_apply, intersectionForm_apply, halfTurnEquiv_apply, halfTurnEquiv_apply]
  simp [Fin.sum_univ_succ, Fin.natAdd]
  ring

private theorem halfTurnEquiv_boundaryClass (j : ZMod 8) :
    halfTurnEquiv (boundaryClass j) = boundaryClass (j + 4) := by
  ext i
  revert j i
  decide

/-- The half-turn fixes both ruling classes and swaps the opposite corner and interior
exceptional classes. -/
def halfTurn : boundaryRotationGroup intersectionForm boundaryClass :=
  ⟨⟨halfTurnEquiv, BilinForm.mem_isometryGroup_iff.mpr halfTurnEquiv_isometry⟩,
    (mem_boundaryRotationGroup_iff _ _).mpr ⟨4, halfTurnEquiv_boundaryClass⟩⟩

/-- In marked coordinates the half-turn interchanges the opposite exceptional coefficients. -/
theorem halfTurn_apply (x : L) :
    halfTurn.val.val x = ![x 0, x 1, x 4, x 5, x 2, x 3, x 8, x 9, x 6, x 7] :=
  halfTurnEquiv_apply x

/-- The half-turn acts on the boundary by the shift through four components. -/
@[simp] theorem halfTurn_boundaryClass (j : ZMod 8) :
    halfTurn.val.val (boundaryClass j) = boundaryClass (j + 4) :=
  halfTurnEquiv_boundaryClass j

/-- The half-turn fixes every class orthogonal to the boundary. -/
@[simp] theorem halfTurn_apply_orthogonal (x : K) :
    halfTurn.val.val x = x := by
  have hg (j : Fin 2) : halfTurn.val.val (orthogonalGenerator j) = orthogonalGenerator j := by
    ext i
    revert j i
    decide
  have h := eq_smul_orthogonalGenerator x.property
  calc
    _ = halfTurn.val.val ((-x.val 2) • orthogonalGenerator 0 +
          (-x.val 3) • orthogonalGenerator 1) := congrArg halfTurn.val.val h
    _ = x := by simpa only [map_add, map_smul, hg] using h.symm

/-- The half-turn has order two. -/
@[simp] theorem halfTurn_mul_self : halfTurn * halfTurn = 1 := by
  apply Subtype.ext (Subtype.ext (LinearEquiv.ext fun x ↦ ?_))
  simp only [Subgroup.coe_mul, Subgroup.coe_one, mul_apply_eq_comp]
  rw [halfTurn_apply, halfTurn_apply]
  ext i
  fin_cases i <;> rfl

/-- The half-turn is a nontrivial boundary rotation. -/
theorem halfTurn_ne_one : halfTurn ≠ 1 := by
  intro h
  have h' := congrArg (fun g : boundaryRotationGroup intersectionForm boundaryClass ↦
    g.val.val (boundaryClass 0) 2) h
  rw [halfTurn_boundaryClass] at h'
  exact (by decide : boundaryClass 4 2 ≠ boundaryClass 0 2) h'

private def shiftedExceptionalDifference (k : ZMod 8) : L :=
  -boundaryClass (0 + k) + (2 : ℤ) • boundaryClass (1 + k) + boundaryClass (2 + k) +
    (3 : ℤ) • boundaryClass (4 + k) + (2 : ℤ) • boundaryClass (5 + k) +
    boundaryClass (6 + k) - (2 : ℤ) • orthogonalGenerator 0

private theorem shiftedExceptionalDifference_zero :
    shiftedExceptionalDifference 0 = (4 : ℤ) • (Pi.single 2 1 - Pi.single 3 1 : L) := by
  ext i
  revert i
  decide

private theorem shift_eq_zero_or_four {g : intersectionForm.isometryGroup} {k : ZMod 8}
    (hg : ∀ j, g.val (boundaryClass j) = boundaryClass (j + k))
    (hK : ∀ x : K, g.val x = x) : k = 0 ∨ k = 4 := by
  have hκ := hK ⟨orthogonalGenerator 0, orthogonalGenerator_mem 0⟩
  have heq : g.val (shiftedExceptionalDifference 0) = shiftedExceptionalDifference k := by
    simp only [shiftedExceptionalDifference, add_zero, map_sub, map_add, map_neg, map_smul, hg]
    exact congrArg (_ - (2 : ℤ) • ·) hκ
  have hd (i : Fin 10) : (4 : ℤ) ∣ shiftedExceptionalDifference k i := by
    rw [← heq, shiftedExceptionalDifference_zero, map_smul, Pi.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  exact (by decide : ∀ k : ZMod 8,
    (∀ i : Fin 10, (4 : ℤ) ∣ shiftedExceptionalDifference k i) → k = 0 ∨ k = 4) k hd

private theorem eq_of_actions {g h : intersectionForm.isometryGroup}
    (hD : ∀ j, g.val (boundaryClass j) = h.val (boundaryClass j))
    (hK : ∀ x : K, g.val x = h.val x) : g = h := by
  let e := intersectionForm.isometryGroupEquivIsometryEquiv
  apply e.injective
  exact boundary_isometry_ext intersectionForm_isSymm intersectionForm_nondegenerate.1
    (BoundaryCycle.span_sup_orthogonal_rat intersectionForm_boundaryClass
      intersectionForm_isSymm intersectionForm_nondegenerate)
    (fun j ↦ by simpa only [e, BilinForm.coe_isometryGroupEquivIsometryEquiv] using hD j)
    (fun x hx ↦ by simpa only [e, BilinForm.coe_isometryGroupEquivIsometryEquiv] using hK ⟨x, hx⟩)

local notation "ρ" => MonoidHom.comp
  (SignedBoundaryIsometryGroup.signedOrthogonalRestriction intersectionForm boundaryClass)
  (SignedBoundaryIsometryGroup.rotationInclusion intersectionForm boundaryClass)

/-- The kernel of the restriction of boundary rotations to the orthogonal lattice
consists of the identity and the half-turn. -/
theorem ker_four_vertex_rotation_restriction : ((ρ).ker : Set _) = {1, halfTurn} := by
  ext g
  simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
  have happly (x : K) : ((ρ g).val x : L) = g.val.val x := by
    simp
  constructor
  · intro hg
    have hfix (x : K) : g.val.val x = x := by rw [← happly, hg]; rfl
    obtain ⟨k, hk⟩ := (mem_boundaryRotationGroup_iff _ _).mp g.property
    rcases shift_eq_zero_or_four hk hfix with rfl | rfl
    · exact Or.inl (Subtype.ext (eq_of_actions (g := g.val) (h := 1)
        (by simpa using hk) (by simpa using hfix)))
    · exact Or.inr (Subtype.ext (eq_of_actions (by simpa using hk)
        (fun x ↦ (hfix x).trans (halfTurn_apply_orthogonal x).symm)))
  · rintro (rfl | rfl)
    · exact map_one _
    · apply Subtype.ext (LinearEquiv.ext fun x ↦ Subtype.ext ?_)
      exact (happly x).trans (halfTurn_apply_orthogonal x)

end QPainleve.FourVertex
