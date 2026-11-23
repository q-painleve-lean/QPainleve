/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Exceptional.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.Cohomology.LongExactSequence
import QPainleve.AlgebraicGeometry.Blowup.Exceptional.Cohomology
import QPainleve.AlgebraicGeometry.Blowup.Point.Cohomology
import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TwistingSheaf

/-!
# Second cohomology of exceptional twists

The inclusion from the preceding exceptional twist induces a surjection on second
cohomology. Its kernel is the image of the exceptional connecting map. The source
of this connecting map is the first cohomology of a line bundle of degree `-m` on
the exceptional projective line. Thus the comparison is an isomorphism for `m ≤ 1`.

The maps are those of Tau Ceti's tensor Cartier sequence and its cohomology sequence.
See [Stacks, Lemma 54.3.4][Stacks] for the exceptional Cartier quotients.

[Stacks]: https://stacks.math.columbia.edu/tag/0AGS
-/

public noncomputable section

open CategoryTheory MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (p : X)

local notation "J" => Scheme.Hom.ker (Scheme.fromSpecResidueField X p)
local notation "Y" => blowup J
local notation "π" => blowupToBase J
local notation "E" => comap J π
local notation:max "twist[" a ", " m "]" =>
  (LineBundleClass.pullback π a * blowupExceptionalClass J ^ (m : ℤ))
local notation:max "δ[" R ", " M "]" =>
  cohomologyδBaseLinear R Y (shortExact_tensor_toPushforwardSubscheme E M) 1 2 rfl

section BaseRing

variable (R : Type u) [CommRing R]
  [Scheme.Over ((X.fromSpecResidueField p).ker.blowup) (Spec (.of R))]

/-- The inclusion `M(-E) → M` on second cohomology for the exceptional Cartier divisor
of a point blowup. -/
def cohomologyTwoExceptionalTwistMap (M : InvertibleSheaf Y) :
    Cohomology (M.obj ⊗ (E).sheaf) 2 →ₗ[R] Cohomology M.obj 2 :=
  cohomologyMapBaseLinear R Y (M.obj ◁ (E).sheafι ≫ (ρ_ M.obj).hom) 2

/-- The second cohomology transition is induced by tensoring the exceptional ideal
inclusion and applying the right unitor. -/
@[simp]
theorem cohomologyTwoExceptionalTwistMap_apply (M : InvertibleSheaf Y)
    (x : Cohomology (M.obj ⊗ (E).sheaf) 2) :
    cohomologyTwoExceptionalTwistMap p R M x =
      cohomologyMap (M.obj ◁ (E).sheafι ≫ (ρ_ M.obj).hom) 2 x := by
  exact congrFun (coe_cohomologyMapBaseLinear R Y
    (M.obj ◁ (E).sheafι ≫ (ρ_ M.obj).hom) 2) x

private theorem cohomologyTwoExceptionalTwistMap_apply_unitor (M : InvertibleSheaf Y)
    (x : Cohomology (M.obj ⊗ (E).sheaf) 2) :
    cohomologyTwoExceptionalTwistMap p R M x =
      cohomologyBaseLinearEquivOfIso R (ρ_ M.obj) 2
        (cohomologyMap (M.obj ◁ (E).sheafι) 2 x) := by
  rw [cohomologyTwoExceptionalTwistMap, cohomologyMapBaseLinear_comp, LinearMap.comp_apply,
    cohomologyBaseLinearEquivOfIso_apply]
  exact congrArg (cohomologyMapBaseLinear R Y (ρ_ M.obj).hom 2)
    (congrFun (coe_cohomologyMapBaseLinear R Y (M.obj ◁ (E).sheafι) 2) x)

/-- The kernel of the exceptional twist transition on second cohomology is the image
of the connecting map from the first cohomology of the exceptional quotient. -/
theorem ker_cohomologyTwoExceptionalTwistMap (M : InvertibleSheaf Y) :
    LinearMap.ker (cohomologyTwoExceptionalTwistMap p R M) = LinearMap.range (δ[R, M.obj]) := by
  let S := (ShortComplex.mk _ _ (E).sheafι_toPushforwardSubscheme).map (tensorLeft M.obj)
  have hS : S.ShortExact := (E).shortExact_tensor_toPushforwardSubscheme M.obj
  have hf : S.f = M.obj ◁ (E).sheafι := rfl
  have h := exact_cohomologyδ_cohomologyMap hS 1 2 rfl
  have he : Function.Exact (δ[R, M.obj]) (cohomologyTwoExceptionalTwistMap p R M) := by
    intro x
    rw [cohomologyTwoExceptionalTwistMap_apply_unitor, ← map_zero
      (cohomologyBaseLinearEquivOfIso R (ρ_ M.obj) 2),
      (cohomologyBaseLinearEquivOfIso R (ρ_ M.obj) 2).injective.eq_iff]
    simpa only [coe_cohomologyδBaseLinear, hf] using h x
  exact he.linearMap_ker_eq

variable {p} (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
  (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
  (a : LineBundleClass X) {m : ℤ} (M : InvertibleSheaf ((X.fromSpecResidueField p).ker.blowup))
  (hM : LineBundleClass.mk M =
    LineBundleClass.pullback (X.fromSpecResidueField p).ker.blowupToBase a *
      (X.fromSpecResidueField p).ker.blowupExceptionalClass ^ m)

include hp hdim hM

/-- The exceptional twist transition on second cohomology is surjective for every
integer twist and any residue field at the center. -/
theorem surjective_cohomologyTwoExceptionalTwistMap :
    Function.Surjective (cohomologyTwoExceptionalTwistMap p R M) := by
  obtain ⟨e⟩ := nonempty_cohomologyAddEquiv_pointBlowup_exceptional_quotient hp hdim a m M hM 2
  let κ := X.residueField p
  let 𝒜 := TauCeti.SymmetricAlgebra.homogeneousSubmodule κ (Fin 2 → κ)
  let b := Pi.basisFun κ (Fin 2)
  have hvan := b.subsingleton_cohomology_proj_of_card_le (Proj.twistingSheaf 𝒜 (-m)) 2 (by decide)
  let hs := @Function.Injective.subsingleton _ _ _ e.injective hvan
  have hS := (E).shortExact_tensor_toPushforwardSubscheme M.obj
  let S := (ShortComplex.mk _ _ (E).sheafι_toPushforwardSubscheme).map (tensorLeft M.obj)
  have hsurj : Function.Surjective (cohomologyMap S.f 2) :=
    fun y ↦ (exact_cohomologyMap_cohomologyMap hS 2 y).mp (hs.allEq _ _)
  have hf : S.f = M.obj ◁ (E).sheafι := rfl
  rw [hf] at hsurj
  intro y
  let u := cohomologyBaseLinearEquivOfIso R (ρ_ M.obj) 2
  obtain ⟨x, hx⟩ := hsurj (u.symm y)
  exact ⟨x, (cohomologyTwoExceptionalTwistMap_apply_unitor p R M x).trans
    ((congrArg u hx).trans (u.apply_symm_apply y))⟩

/-- Second cohomology of the twist is the cokernel of the exceptional connecting
map from the preceding Cartier sequence. The equivalence is induced by the inclusion. -/
def cohomologyTwoExceptionalTwistQuotientEquiv :
    (Cohomology (M.obj ⊗ (E).sheaf) 2 ⧸ LinearMap.range (δ[R, M.obj])) ≃ₗ[R] Cohomology M.obj 2 :=
  (LinearMap.exact_iff.mpr (ker_cohomologyTwoExceptionalTwistMap p R M)).linearEquivOfSurjective
    (surjective_cohomologyTwoExceptionalTwistMap R hp hdim a M hM)

/-- The quotient equivalence sends the class of a cohomology element to its image
under the Cartier inclusion. -/
@[simp]
theorem cohomologyTwoExceptionalTwistQuotientEquiv_mk
    (x : Cohomology (M.obj ⊗ (E).sheaf) 2) :
    cohomologyTwoExceptionalTwistQuotientEquiv R hp hdim a M hM (Submodule.Quotient.mk x) =
      cohomologyTwoExceptionalTwistMap p R M x := by
  rfl

/-- For twists of degree at most one, the transition on second cohomology is bijective
because the exceptional quotient has vanishing first and second cohomology. -/
theorem bijective_cohomologyTwoExceptionalTwistMap (hm : m ≤ 1) :
    Function.Bijective (cohomologyTwoExceptionalTwistMap p R M) := by
  obtain ⟨e⟩ := nonempty_cohomologyAddEquiv_pointBlowup_exceptional_quotient hp hdim a m M hM 1
  let b := Pi.basisFun (X.residueField p) (Fin 2)
  have hvan := b.subsingleton_cohomology_twistingSheaf_of_neg_card_lt
    (m := -m) (q := 1) (by simp only [Fintype.card_fin]; omega) (by decide)
  let hs := @Function.Injective.subsingleton _ _ _ e.injective hvan
  refine ⟨LinearMap.ker_eq_bot.mp ?_, surjective_cohomologyTwoExceptionalTwistMap R hp hdim a M hM⟩
  rw [ker_cohomologyTwoExceptionalTwistMap, LinearMap.range_eq_bot.mpr]
  ext x
  rw [hs.allEq x 0, map_zero, LinearMap.zero_apply]

end BaseRing

section Field

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

variable {p} (hp : IsClosed ({p} : Set X)) [IsRegularLocalRing (X.presheaf.stalk p)]
  (hdim : ringKrullDim (X.presheaf.stalk p) = 2)
  (a : LineBundleClass X) {m : ℤ} (M : InvertibleSheaf ((X.fromSpecResidueField p).ker.blowup))
  (hM : LineBundleClass.mk M =
    LineBundleClass.pullback (X.fromSpecResidueField p).ker.blowupToBase a *
      (X.fromSpecResidueField p).ker.blowupExceptionalClass ^ m)

include hp hdim hM

/-- At a rational blowup center, the dimension drop in `H²` from `(m - 1)E` to `mE`
is between zero and `max (m - 1) 0`. -/
theorem finrank_cohomology_two_exceptional_twist_bounds
    (hrat : IsIso (X.fromSpecResidueField p ≫ (X ↘ Spec (.of k)))) :
    letI : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    ∀ [FiniteDimensional k (Cohomology (M.obj ⊗ (E).sheaf) 2)],
    Module.finrank k (Cohomology M.obj 2) ≤
      Module.finrank k (Cohomology (M.obj ⊗ (E).sheaf) 2) ∧
    Module.finrank k (Cohomology (M.obj ⊗ (E).sheaf) 2) ≤
      Module.finrank k (Cohomology M.obj 2) + (m - 1).toNat := by
  intro _
  let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  have hclass : LineBundleClass.mk M = LineBundleClass.pullback π a *
      (LineBundleClass.mk (isEffectiveCartier_comap_blowupToBase J).toInvertibleSheaf) ^
        (-m) := by
    simpa only [blowupExceptionalClass_def, inv_zpow'] using hM
  obtain ⟨e⟩ := nonempty_cohomologyLinearEquiv_pointBlowup_exceptional_quotient
    p k hp hdim hrat a m M hclass 1
  have := (Pi.basisFun k (Fin 2)).finite_cohomology_twistingSheaf (-m) 1
  have : Module.Finite k (Cohomology (M.obj ⊗ (E).pushforwardSubscheme) 1) :=
    Module.Finite.equiv e.symm
  let boundary : Cohomology (M.obj ⊗ (E).pushforwardSubscheme) 1 →ₗ[k]
      Cohomology (M.obj ⊗ (E).sheaf) 2 := δ[k, M.obj]
  have hbound : Module.finrank k (LinearMap.range (δ[k, M.obj])) ≤ (m - 1).toNat := calc
    _ ≤ Module.finrank k (Cohomology (M.obj ⊗ (E).pushforwardSubscheme) 1) :=
      LinearMap.finrank_range_le boundary
    _ = _ := finrank_cohomology_one_pointBlowup_exceptional_quotient p k hp hdim hrat a m M hclass
  let f := cohomologyTwoExceptionalTwistMap p k M
  have hdrop := f.finrank_range_add_finrank_ker
  dsimp only [f] at hdrop
  rw [LinearMap.range_eq_top.mpr (surjective_cohomologyTwoExceptionalTwistMap k hp hdim a M hM),
    finrank_top, ker_cohomologyTwoExceptionalTwistMap] at hdrop
  constructor
  · rw [← hdrop]
    exact Nat.le_add_right _ _
  · rw [← hdrop]
    exact Nat.add_le_add_left hbound _

variable [IsLocallyNoetherian X]

omit hM in
/-- Second cohomology is unchanged from the base line bundle for every exceptional twist
with coefficient at most one. The comparison uses the pulled-back line bundle and the
inclusions between successive twists. -/
theorem nonempty_cohomologyTwoPointBlowupExceptionalTwistLinearEquiv
    (L : InvertibleSheaf X) (hM : LineBundleClass.mk M = twist[LineBundleClass.mk L, m])
    (hm : m ≤ 1) :
    letI : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
    Nonempty (Cohomology L.obj 2 ≃ₗ[k] Cohomology M.obj 2) := by
  let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  let a := LineBundleClass.mk L
  have prev {t : ℤ} {A B : InvertibleSheaf Y}
      (hA : LineBundleClass.mk A = twist[a, t - 1])
      (hB : LineBundleClass.mk B = twist[a, t]) (ht : t ≤ 1) :
      Nonempty (Cohomology A.obj 2 ≃ₗ[k] Cohomology B.obj 2) := by
    obtain ⟨e⟩ := exists_iso_tensor_exceptional_ideal_pointBlowup_twist p a t
      (by simpa only [blowupExceptionalClass_def, inv_zpow'] using hA)
      (by simpa only [blowupExceptionalClass_def, inv_zpow'] using hB)
    exact ⟨(cohomologyBaseLinearEquivOfIso k e 2).trans
      (LinearEquiv.ofBijective _ (bijective_cohomologyTwoExceptionalTwistMap k hp hdim a B hB ht))⟩
  let P := (InvertibleSheaf.pullback π).obj L
  obtain ⟨pull⟩ := nonempty_cohomologyLinearEquiv_pointBlowup_pullback p k hp hdim L 2
  have zero (B : InvertibleSheaf Y) (hB : LineBundleClass.mk B = twist[a, 0]) :
      Nonempty (Cohomology L.obj 2 ≃ₗ[k] Cohomology B.obj 2) := by
    have hP : LineBundleClass.mk P = LineBundleClass.mk B := by
      rw [hB, zpow_zero, mul_one]
      exact (LineBundleClass.pullback_mk π L).symm
    obtain ⟨e⟩ := LineBundleClass.mk_eq_mk_iff.mp hP
    exact ⟨pull.trans (cohomologyBaseLinearEquivOfIso k e 2)⟩
  by_cases hone : m = 1
  · subst m
    have hP : LineBundleClass.mk P = twist[a, 1 - 1] := by
      simp only [sub_self, zpow_zero, mul_one, a, LineBundleClass.pullback_mk, P]
    obtain ⟨e⟩ := prev hP hM le_rfl
    exact ⟨pull.trans e⟩
  have hneg : ∃ n : ℕ, m = -(n : ℤ) := ⟨(-m).toNat, by omega⟩
  obtain ⟨n, rfl⟩ := hneg
  clear hm hone
  induction n generalizing M with
  | zero => exact zero M (by simpa only [Nat.cast_zero, neg_zero, a] using hM)
  | succ n ih =>
    let t := -(n : ℤ)
    obtain ⟨B, hB⟩ := LineBundleClass.mk_surjective (twist[a, t])
    have hM' : LineBundleClass.mk M = twist[a, t - 1] := by
      simpa only [t, Nat.cast_succ, neg_add', sub_eq_add_neg, add_comm, a] using hM
    obtain ⟨e⟩ := prev hM' hB (by dsimp [t]; omega)
    obtain ⟨e'⟩ := ih B hB
    exact ⟨e'.trans e.symm⟩

include k in
omit hM in
/-- If a line bundle has vanishing second cohomology, every exceptional twist of its
pullback to a point blowup also has vanishing second cohomology. -/
theorem subsingleton_cohomology_two_pointBlowup_exceptional_twist
    (L : InvertibleSheaf X) (hL : Subsingleton (Cohomology L.obj 2))
    (hM : LineBundleClass.mk M = twist[LineBundleClass.mk L, m]) :
    Subsingleton (Cohomology M.obj 2) := by
  let : Scheme.Over Y (Spec (.of k)) := ⟨π ≫ X ↘ Spec (.of k)⟩
  by_cases hm : m ≤ 0
  · obtain ⟨e⟩ := nonempty_cohomologyTwoPointBlowupExceptionalTwistLinearEquiv
      k hp hdim M L hM (by omega)
    exact e.surjective.subsingleton
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n := ⟨m.toNat, by omega⟩
  clear hm
  induction n generalizing M with
  | zero =>
    obtain ⟨e⟩ := nonempty_cohomologyTwoPointBlowupExceptionalTwistLinearEquiv
      k hp hdim M L hM (by omega)
    exact e.surjective.subsingleton
  | succ n ih =>
    obtain ⟨A, hA⟩ := LineBundleClass.mk_surjective (twist[LineBundleClass.mk L, (n : ℤ)])
    have := ih A hA
    obtain ⟨e⟩ := exists_iso_tensor_exceptional_ideal_pointBlowup_twist p
      (LineBundleClass.mk L) (n + 1)
      (by simpa only [add_sub_cancel_right, blowupExceptionalClass_def, inv_zpow'] using hA)
      (by simpa only [Nat.cast_succ, blowupExceptionalClass_def, inv_zpow'] using hM)
    have := (cohomologyBaseLinearEquivOfIso k e 2).surjective.subsingleton
    exact (surjective_cohomologyTwoExceptionalTwistMap k hp hdim _ M hM).subsingleton

end Field

end AlgebraicGeometry.Scheme.IdealSheafData
