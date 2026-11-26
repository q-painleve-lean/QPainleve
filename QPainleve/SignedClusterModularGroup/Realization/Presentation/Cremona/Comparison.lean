/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Algebra.Cluster.Word.ModularGroup
public import QPainleve.SignedClusterModularGroup.Boundary.Isometry

/-!
# Cluster modular group comparisons with Cremona isometries

A Cremona comparison records Picard pullback and the ordered branch sign on
opposite signed cluster maps. The boundary length determines whether pullback
alone gives an equivalence or the sign supplies a separate factor. In the
latter case the sign kernel identifies unsigned maps with the Cremona group.
-/

public noncomputable section

open MulOpposite QPainleve.Cluster

namespace QPainleve.SignedClusterModularGroup

variable {k : Type*} [Field k] {ι : Type*} [DecidableEq ι]
  {E : SkewExchangeMatrix ι} {n : ℕ} {C : Type*} [Group C]

local notation "Γs" => (SignedClusterModularGroup k E)ᵐᵒᵖ
local notation "Γ" => (ClusterModularGroup k E)ᵐᵒᵖ
local notation "incl" => MonoidHom.op (clusterModularGroupInclusion k E)

/-- A Cremona projection and branch sign for a seed presented on a cycle of length `n`.
For at least three components the projection is injective. For one or two components
the projection together with the sign is bijective. The sign kernel consists of the
unsigned cluster maps. -/
@[ext]
structure ClusterCremonaComparison (E : SkewExchangeMatrix ι) (n : ℕ) (C : Type*) [Group C] where
  /-- Picard pullback, viewed as a Cremona isometry. -/
  projection : (SignedClusterModularGroup k E)ᵐᵒᵖ →* C
  /-- The ordered branch sign on the opposite signed group. -/
  sign : (SignedClusterModularGroup k E)ᵐᵒᵖ →* ℤˣ
  /-- Every Cremona isometry is realized by a signed cluster map. -/
  projection_surjective : Function.Surjective projection
  /-- On a cycle with at least three components, pullback determines the signed map. -/
  projection_injective (hn : 3 ≤ n) : Function.Injective projection
  /-- On a cycle with at most two components, pullback and sign are independent coordinates. -/
  prod_bijective (hn : n ≤ 2) : Function.Bijective (projection.prod sign)
  /-- Positive sign characterizes the unsigned cluster maps. -/
  sign_ker_unop : sign.ker.unop = (clusterModularGroupInclusion k E).range

namespace ClusterCremonaComparison

variable (P : ClusterCremonaComparison (k := k) E n C)

/-- For at least three boundary components, Picard pullback is a Cremona equivalence. -/
def signedEquiv (hn : 3 ≤ n) : Γs ≃* C :=
  MulEquiv.ofBijective P.projection ⟨P.projection_injective hn, P.projection_surjective⟩

/-- The large-boundary equivalence evaluates by the Cremona projection. -/
@[simp]
theorem signedEquiv_apply (hn : 3 ≤ n) (x : Γs) :
    P.signedEquiv hn x = P.projection x :=
  (rfl)

/-- For one or two components, the signed equivalence also records the branch sign. -/
def signedProdEquiv (hn : n ≤ 2) : Γs ≃* C × ℤˣ :=
  MulEquiv.ofBijective (P.projection.prod P.sign) (P.prod_bijective hn)

/-- The product equivalence evaluates by Picard pullback and the branch sign. -/
@[simp]
theorem signedProdEquiv_apply (hn : n ≤ 2) (x : Γs) :
    P.signedProdEquiv hn x = (P.projection x, P.sign x) :=
  (rfl)

/-- An opposite signed map comes from an unsigned map exactly when its branch sign is positive. -/
theorem sign_eq_one_iff_mem_range (x : Γs) : P.sign x = 1 ↔ x ∈ (incl).range := by
  have hx : x ∈ P.sign.ker ↔ x.unop ∈ P.sign.ker.unop := by
    rw [Subgroup.mem_unop, op_unop]
  rw [← MonoidHom.mem_ker, hx, P.sign_ker_unop]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨op u, by simp only [MonoidHom.op_apply_apply, Function.comp_apply, unop_op, hu,
      op_unop]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.unop, by simp only [MonoidHom.op_apply_apply, Function.comp_apply, unop_op]⟩

/-- An unsigned map has positive branch sign. -/
@[simp]
theorem sign_apply_inclusion (x : ClusterModularGroup k E) :
    P.sign (op (clusterModularGroupInclusion k E x)) = 1 :=
  (P.sign_eq_one_iff_mem_range _).mpr ⟨op x, by simp⟩

/-- For one or two components, unsigned cluster maps identify with Cremona isometries. -/
def unsignedEquiv (hn : n ≤ 2) : Γ ≃* C := by
  refine MulEquiv.ofBijective (P.projection.comp incl) ⟨?_, ?_⟩
  · intro x y hxy
    have hincl : Function.Injective incl :=
      op_injective.comp ((clusterModularGroupInclusion_injective k E).comp unop_injective)
    apply hincl
    apply (P.signedProdEquiv hn).injective
    simpa only [signedProdEquiv_apply, MonoidHom.op_apply_apply, Function.comp_apply,
      sign_apply_inclusion, MonoidHom.comp_apply, Prod.mk.injEq, and_true] using hxy
  · intro g
    obtain ⟨x, hx⟩ := (P.signedProdEquiv hn).surjective (g, 1)
    rw [signedProdEquiv_apply] at hx
    obtain ⟨u, rfl⟩ := (P.sign_eq_one_iff_mem_range x).mp (congrArg Prod.snd hx)
    exact ⟨u, congrArg Prod.fst hx⟩

/-- The unsigned equivalence evaluates by inclusion followed by Picard pullback. -/
@[simp]
theorem unsignedEquiv_apply (hn : n ≤ 2) (x : Γ) :
    P.unsignedEquiv hn x = P.projection (incl x) :=
  (rfl)

/-- Under the small-boundary product equivalence, the unsigned inclusion is the Cremona factor. -/
theorem signedProdEquiv_apply_inclusion (hn : n ≤ 2) (x : Γ) :
    P.signedProdEquiv hn (incl x) = (P.unsignedEquiv hn x, 1) := by
  simp only [signedProdEquiv_apply, unsignedEquiv_apply, MonoidHom.op_apply_apply,
    Function.comp_apply, sign_apply_inclusion]

section Picard

open QPainleve.SignedBoundaryIsometryGroup

variable {L : Type*} [AddCommGroup L] {B : LinearMap.BilinForm ℤ L} {d : ZMod n → L}
  (Θ : (SignedClusterModularGroup k E)ᵐᵒᵖ ≃* ↥(signedBoundaryIsometryGroup B d))
  (hΘ : ((SignedBoundaryIsometryGroup.sign B d).comp Θ.toMonoidHom).ker.unop =
    (clusterModularGroupInclusion k E).range)
  (π : signedBoundaryIsometryGroup B d →* C) (hsurj : Function.Surjective π)
  (hinj : 3 ≤ n → Function.Injective π)
  (eprod : n ≤ 2 → signedBoundaryIsometryGroup B d ≃* C × ℤˣ)
  (heprod : ∀ hn g, eprod hn g = (π g, SignedBoundaryIsometryGroup.sign B d g))

/-- Transport a Cremona projection and its small-boundary product equivalence along a
signed Picard equivalence that identifies the sign kernel with the unsigned maps. -/
def ofPicardEquiv : ClusterCremonaComparison (k := k) E n C where
  projection := π.comp Θ.toMonoidHom
  sign := (SignedBoundaryIsometryGroup.sign B d).comp Θ.toMonoidHom
  projection_surjective := hsurj.comp Θ.surjective
  projection_injective hn := (hinj hn).comp Θ.injective
  prod_bijective hn := by
    have h : (⇑((π.comp Θ.toMonoidHom).prod
        ((SignedBoundaryIsometryGroup.sign B d).comp Θ.toMonoidHom))) =
        ⇑(Θ.trans (eprod hn)) := funext fun x ↦ (heprod hn (Θ x)).symm
    rw [h]
    exact (Θ.trans (eprod hn)).bijective
  sign_ker_unop := hΘ

/-- The transported Cremona projection evaluates on the signed Picard image. -/
@[simp]
theorem ofPicardEquiv_projection_apply (x : Γs) :
    (ofPicardEquiv Θ hΘ π hsurj hinj eprod heprod).projection x = π (Θ x) :=
  (rfl)

/-- The sign of the transported projection is the sign of the signed Picard image. -/
@[simp]
theorem ofPicardEquiv_sign_apply (x : Γs) :
    (ofPicardEquiv Θ hΘ π hsurj hinj eprod heprod).sign x =
      SignedBoundaryIsometryGroup.sign B d (Θ x) :=
  (rfl)

end Picard

end ClusterCremonaComparison

end QPainleve.SignedClusterModularGroup
