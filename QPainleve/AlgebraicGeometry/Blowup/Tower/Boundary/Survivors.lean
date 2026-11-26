/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Boundary.Numbering
public import QPainleve.AlgebraicGeometry.Curves.Node.NumberedPrime

import QPainleve.AlgebraicGeometry.Blowup.Tower.Modification
import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.ComponentOrder
import QPainleve.AlgebraicGeometry.Morphisms.Smooth.Factorial
import TauCeti.AlgebraicGeometry.Morphisms.Modification.Composition
import TauCeti.AlgebraicGeometry.Noetherian
import TauCeti.Data.ZMod.FinEquiv

/-!
# Numbering boundary primes that survive a blowup tower

The schematic image of a numbered anticanonical boundary inherits its branch
orientation. Given the surviving components in increasing order, start the
image numbering at the first of them. This identifies the boundary primes on a
contracted toric model with the surviving entries of the original ray list.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme Scheme.IdealSheafData LineBundleClass

universe u v

namespace QPainleve.BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k] [NeZero (2 : k)] {X Y Z : Scheme.{u}}
  [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
  [IsIntegral X] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
  [Z.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (Z ↘ Spec (.of k))]
  {B : Z.IdealSheafData} [PrestableFamily (B.subscheme ↘ Spec (.of k))]
  {ι : Type v} {a : ι → (B.subscheme ↘ Spec (.of k)).smoothLocus}
  {m n : ℕ} [NeZero m] [NeZero n]

local notation "S" => Spec (CommRingCat.of k)
local notation "K[" W "]" => mk (QPainleve.canonicalBundle k W 2)

variable (hB : B.IsEffectiveCartier) (A : Scheme.NodalCycleNumbering a m)
  {f : Z ⟶ X} (s : Fin n ↪o Fin m)

local notation "prime[" j "]" => A.boundaryPrimeEquiv hB (ZMod.finEquiv m j)
local notation "D" => B.map f

omit [NeZero (2 : k)] [X.Over S] [X.IsProjectiveOver k]
  [SmoothOfRelativeDimension 2 (X ↘ S)] [SmoothOfRelativeDimension 2 (Z ↘ S)] [NeZero n] in
private theorem bijective_survivingBoundaryPrimes [IsNormalScheme X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsReduced Z] [IsModification f]
    (hs : ∀ j : Fin m, f (prime[j]).val ∈ (B.map f).boundaryPrimes ↔ j ∈ Set.range s) :
    Function.Bijective (fun i : Fin n ↦
      (⟨f (prime[s i]).val, (hs (s i)).mpr (Set.mem_range_self i)⟩ : (D).boundaryPrimes)) := by
  have h := B.bijOn_boundaryPrimes_map f
  have hmem (i : Fin n) : (prime[s i]).val ∈ B.boundaryPrimes ∩ f ⁻¹' (D).boundaryPrimes :=
    ⟨(prime[s i]).property, (hs (s i)).mpr (Set.mem_range_self i)⟩
  constructor
  · intro i j hij
    exact s.injective ((ZMod.finEquiv m).injective ((A.boundaryPrimeEquiv hB).injective
      (Subtype.ext (h.injOn (hmem i) (hmem j) (congrArg Subtype.val hij)))))
  · intro y
    obtain ⟨x, hx, hxy⟩ := h.surjOn y.property
    obtain ⟨j, hj⟩ := ((ZMod.finEquiv m).toEquiv.trans (A.boundaryPrimeEquiv hB)).surjective
      ⟨x, hx.1⟩
    have heq : (prime[j]).val = x := congrArg Subtype.val hj
    obtain ⟨i, rfl⟩ := (hs j).mp (heq.symm ▸ hx.2)
    exact ⟨i, Subtype.ext ((congrArg f heq).trans hxy)⟩

/-- Number the image of a nodal anticanonical boundary by the surviving primes in the
original numbering. The given increasing enumeration determines the length and
origin of the descended cycle. Its two ordered branches at each node inherit
their order from the source subdivision, including for one or two survivors. -/
theorem exists_numbering_of_anticanonical_boundary_tower_blowdown_of_survivors
    {l : ℕ} {T : BlowupTower X l Y} (hT : IsClosedPointTower X T)
    (e : Z ≅ Y) [f.IsOver S] (he : e.hom ≫ T.toBase = f) (hcan : mk hB.toInvertibleSheaf = K[Z]) :
    letI := LocallyOfFiniteType.isLocallyNoetherian (X ↘ S)
    letI := SmoothOfRelativeDimension.smooth 2 (Z ↘ S)
    letI := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ S)
    (∀ j : Fin m, f (prime[j]).val ∈ (D).boundaryPrimes ↔ j ∈ Set.range s) →
    ∃ (hD : (D).IsEffectiveCartier) (_ : PrestableFamily ((D).subscheme ↘ S)),
      mk hD.toInvertibleSheaf = K[X] ∧
      ∃ (C : Scheme.NodalCycleNumbering
          (PEmpty.elim : PEmpty.{v + 1} → ((D).subscheme ↘ S).smoothLocus) n)
        (g : B.subscheme ⟶ (D).subscheme),
        g ≫ (D).subschemeι = B.subschemeι ≫ f ∧ g.IsOver S ∧
        g.IsOrientedCycleSubdivision A C ∧
        ∀ j : Fin n, f (prime[s j]).val =
          (C.boundaryPrimeEquiv hD (ZMod.finEquiv n j)).val := by
  intro hs
  let : IsNoetherian X := isNoetherian_of_finiteType (X ↘ S)
  let : Smooth (Z ↘ S) := SmoothOfRelativeDimension.smooth 2 _
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (Z ↘ S)
  let := (X ↘ S).uniqueFactorizationMonoid_stalk_of_smoothOfRelativeDimension_two
  let : IsNormalScheme X := IsNormalScheme.of_uniqueFactorizationMonoid_stalk
  let : IsIntegral Y := hT.isIntegral (X ↘ S)
  let : IsReduced Z := isReduced_of_isOpenImmersion e.hom
  let : IsModification T.toBase :=
    hT.isModification_of_smoothOfRelativeDimension_two (X ↘ S)
  let : IsModification e.hom := IsModification.of_isIso e.hom
  let : IsModification f := he ▸ inferInstanceAs (IsModification (e.hom ≫ T.toBase))
  obtain ⟨hD, hpre, hK, p, hp, C, g, hg, hsub⟩ :=
    hT.exists_numbering_of_anticanonical_boundary_tower_blowdown_of_iso e he hB A hcan
  have hgOver : g.IsOver S := ⟨by
    rw [(D).over_eq_subschemeι_comp, ← Category.assoc, hg, Category.assoc, comp_over,
      B.over_eq_subschemeι_comp]⟩
  let : PrestableFamily ((D).subscheme ↘ S) := hpre
  let F := Equiv.ofBijective _ (bijective_survivingBoundaryPrimes hB A s hs)
  have hlen : p = n := by
    simpa only [Nat.card_zmod, Nat.card_fin] using
      Nat.card_congr ((C.boundaryPrimeEquiv hD).trans F.symm)
  subst p
  obtain ⟨t, ht, hpoint⟩ := hsub.exists_rotate_numbering_of_surviving_components s (by
    intro j
    obtain ⟨i, hi⟩ := F.surjective (C.boundaryPrimeEquiv hD j)
    refine ⟨i, (D).subschemeι.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
    simpa only [F, Equiv.ofBijective_apply, NodalCycleNumbering.boundaryPrimeEquiv_apply_val] using
      (congrArg Subtype.val hi))
  refine ⟨hD, hpre, hK, C.rotate t, g, hg, hgOver, ht, fun j ↦ ?_⟩
  rw [NodalCycleNumbering.boundaryPrimeEquiv_apply_val,
    NodalCycleNumbering.boundaryPrimeEquiv_apply_val, ← Scheme.Hom.comp_apply B.subschemeι,
    ← hg, Scheme.Hom.comp_apply g, hpoint]

end QPainleve.BlowupTower.IsClosedPointTower
