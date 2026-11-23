/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.CharacterTorus.Scheme

/-!
# Distinct center parameters on each boundary component

Given a finite set of center labels assigned to boundary components, the parameter space
where same-component centers are distinct is open. Its complement is the union of
the same-component coordinate diagonals. Over a field, this open is dense.
-/

public noncomputable section

open AlgebraicGeometry Multiplicative TopologicalSpace
open TauCeti

namespace QPainleve.CharacterTorus

universe u

variable (k : Type u) [CommRing k] {ι : Type u} [Finite ι] [DecidableEq ι] {R : Type*}

local notation "A" => (ι → ℤ)
local notation "X" j:arg => (AddMonoidAlgebra.single (Pi.single j (1 : ℤ) : A) (1 : k))

/-- The center parameters on any one component must be pairwise different. -/
def distinctCentersOpen (s : ι → R) : (scheme k A).Opens :=
  ⨅ p : {p : ι × ι // p.1 ≠ p.2 ∧ s p.1 = s p.2},
    PrimeSpectrum.basicOpen (X p.val.1 - X p.val.2)

/-- A center parameter lies in the open if each same-component difference avoids its prime ideal. -/
theorem mem_distinctCentersOpen_iff (s : ι → R) (x : scheme k A) :
    x ∈ distinctCentersOpen k s ↔
      ∀ i j : ι, i ≠ j → s i = s j → X i - X j ∉ x.asIdeal := by
  let y : PrimeSpectrum (AddMonoidAlgebra k A) := x
  let U (p : {p : ι × ι // p.1 ≠ p.2 ∧ s p.1 = s p.2}) :
      Opens (PrimeSpectrum (AddMonoidAlgebra k A)) :=
    PrimeSpectrum.basicOpen (X p.val.1 - X p.val.2)
  -- The scheme is affine, so compute the finite intersection in the prime spectrum.
  change y ∈ ((⨅ p, U p : Opens (PrimeSpectrum (AddMonoidAlgebra k A))) : Set _) ↔ _
  rw [Opens.coe_iInf]
  simp only [Set.mem_iInter, U, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
    Subtype.forall, Prod.forall, and_imp]
  rfl

/-- Injectively changing the component labels preserves the distinct-center open. -/
theorem distinctCentersOpen_comp_of_injective {S : Type*} (s : ι → R) {f : R → S}
    (hf : Function.Injective f) : distinctCentersOpen k (f ∘ s) = distinctCentersOpen k s := by
  apply SetLike.ext
  intro x
  simp only [mem_distinctCentersOpen_iff, Function.comp_apply, hf.eq_iff]

/-- At a point over a field, the center differences are tested on the coordinate units. -/
@[simp]
theorem point_mem_distinctCentersOpen_iff {K : Type u} [Field K] (s : ι → R)
    (c : Multiplicative A →* Kˣ) (x : Spec (.of K)) :
    ((pointsEquiv K A).symm c).val x ∈ distinctCentersOpen K s ↔
      ∀ i j : ι, i ≠ j → s i = s j →
        c (ofAdd (Pi.single i 1)) ≠ c (ofAdd (Pi.single j 1)) := by
  rw [mem_distinctCentersOpen_iff, pointsEquiv_symm_apply_val]
  let f := (DiagonalizableGroup.point c).comp
    (AddMonoidAlgebra.toMultiplicativeAlgEquiv K K A).toAlgHom
  let y : PrimeSpectrum K := x
  let := y.isPrime
  have hy : y.asIdeal = ⊥ := Ideal.eq_bot_of_prime y.asIdeal
  -- On the affine presentation the image point is the inverse image of the zero ideal.
  change (∀ i j : ι, i ≠ j → s i = s j →
    f (AddMonoidAlgebra.single (Pi.single i 1) 1 - AddMonoidAlgebra.single (Pi.single j 1) 1)
      ∉ y.asIdeal) ↔ _
  simp [f, hy, sub_eq_zero, ← Units.ext_iff, DiagonalizableGroup.point_single]

/-- The same-component diagonals omit the generic point of the center torus. -/
theorem nonempty_distinctCentersOpen {K : Type u} [Field K] (s : ι → R) :
    (distinctCentersOpen K s : Set (scheme K A)).Nonempty := by
  let := Fintype.ofFinite ι
  let : HasUniqueDiv A := hasUniqueDiv_of_free_int
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, (mem_distinctCentersOpen_iff K s _).mpr ?_⟩
  intro i j hij _
  simp only [Ideal.mem_bot, sub_ne_zero]
  intro h
  have he : (Pi.single i (1 : ℤ) : A) ≠ Pi.single j 1 := by
    intro hsingle
    have hi := congrFun hsingle i
    simp [Pi.single_eq_of_ne hij] at hi
  exact he ((AddMonoidAlgebra.single_left_inj (one_ne_zero (α := K))).mp h)

end QPainleve.CharacterTorus
