/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver

import Mathlib.Order.OrderIsoNat
import QPainleve.AlgebraicGeometry.Cohomology.CartierPairing
import QPainleve.AlgebraicGeometry.Cohomology.Projective
import QPainleve.AlgebraicGeometry.EffectiveCartierDivisor.Twist

/-!
# Lifting sections after twisting along a Cartier divisor

For an effective Cartier divisor with trivial conormal line bundle, all twists
of a line bundle along the divisor have isomorphic restrictions. If their
restricted first cohomology vanishes, the ambient first cohomology maps are
surjective. Finite dimensionality makes their dimensions stabilize, at which
point the connecting maps vanish and every section on the divisor lifts.

The stabilization argument is the section-lifting step in O. Debarre,
[*Introduction to Mori Theory*, Theorem 4.1][Debarre].

[Debarre]: https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M22.pdf#page=42
-/

public section

open CategoryTheory MonoidalCategory Filter
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.LineBundleClass hiding mk pullback
open TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- If the ideal-sheaf inclusion is injective on first cohomology after tensoring
with a line bundle, global sections of the line bundle lift from the closed subscheme. -/
theorem surjective_pullbackSectionsLE_of_injective_cohomologyMap (M : InvertibleSheaf X)
    (h : Function.Injective
      (cohomologyMap (M.obj ◁ (I.sheafι : I.sheaf ⟶ 𝟙_ X.Modules)) 1)) :
    Function.Surjective (I.subschemeι.pullbackSectionsLE M.obj ⊤ ⊤ (by simp)) := by
  have hS := I.shortExact_tensor_toPushforwardSubscheme M.obj
  have hδ (y) : cohomologyδ hS 0 1 rfl y = 0 :=
    h ((exact_cohomologyδ_cohomologyMap hS 0 1 rfl _).mpr ⟨y, rfl⟩
      |>.trans (map_zero _).symm)
  have hs : Function.Surjective (cohomologyMap (M.obj ◁ I.toPushforwardSubscheme) 0) :=
    fun y ↦ (exact_cohomologyMap_cohomologyδ hS 0 1 rfl y).mp (hδ y)
  have hq : Function.Surjective ((M.obj ◁ I.toPushforwardSubscheme).app ⊤) := by
    intro y
    obtain ⟨x, hx⟩ := hs ((cohomologyZeroEquiv _).symm y)
    refine ⟨cohomologyZeroEquiv _ x, ?_⟩
    rw [← cohomologyZeroEquiv_cohomologyMap, hx, AddEquiv.apply_symm_apply]
  have hunit := (ConcreteCategory.bijective_of_isIso ((ρ_ M.obj).inv.app ⊤)).2
  exact I.surjective_pullbackSectionsLE_of_surjective_tensorRestriction M (hq.comp hunit)

private theorem eventually_injective_cohomologyMap_tensorIdeal (k : Type u) [Field k]
    [X.Over (Spec (.of k))] [X.IsProjectiveOver k] (M : ℕ → InvertibleSheaf X)
    (e : ∀ n, (M (n + 1)).obj ⊗ I.sheaf ≅ (M n).obj)
    (hvan : ∀ᶠ n : ℕ in atTop,
      Subsingleton (Cohomology ((M n).obj ⊗ I.pushforwardSubscheme) 1)) :
    ∀ᶠ n : ℕ in atTop, Function.Injective (cohomologyMap ((M (n + 1)).obj ◁ I.sheafι) 1) := by
  let d (n : ℕ) := Module.finrank k (Cohomology (M n).obj 1)
  let a (n : ℕ) := (M (n + 1)).obj
  let src (n : ℕ) := cohomologyBaseLinearEquivOfIso k (e n).symm 1
  let tgt (n : ℕ) := cohomologyBaseLinearEquivOfIso k (ρ_ (a n)) 1
  let map (n : ℕ) := (tgt n).toLinearMap.comp
    ((cohomologyMapBaseLinear k X (a n ◁ I.sheafι) 1).comp (src n).toLinearMap)
  have hmaps : ∀ᶠ n : ℕ in atTop, Function.Surjective (map n) := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hvan
    filter_upwards [eventually_ge_atTop N] with n hn
    have hq : Subsingleton (Cohomology (a n ⊗ I.pushforwardSubscheme) 1) :=
      hN (n + 1) (hn.trans (Nat.le_succ n))
    have hS := I.shortExact_tensor_toPushforwardSubscheme (a n)
    have hs : Function.Surjective (cohomologyMap (a n ◁ I.sheafι) 1) :=
      fun y ↦ (exact_cohomologyMap_cohomologyMap hS 1 y).mp (hq.elim _ _)
    simpa only [map, LinearMap.coe_comp, LinearEquiv.coe_coe, coe_cohomologyMapBaseLinear] using
      (tgt n).surjective.comp (hs.comp (src n).surjective)
  have hfinite (n : ℕ) : Module.Finite k (Cohomology (M n).obj 1) :=
    moduleFinite_cohomology_of_isProjectiveOver k _ _
  have hstep : ∀ᶠ n : ℕ in atTop, d (n + 1) ≤ d n := hmaps.mono fun n hn ↦ by
    have := hfinite n
    exact LinearMap.finrank_le_finrank_of_surjective hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
  have hanti : Antitone (fun n ↦ d (N + n)) := antitone_nat_of_succ_le fun n ↦
    hN (N + n) (Nat.le_add_right ..)
  obtain ⟨m, hm⟩ := WellFoundedLT.antitone_chain_condition hanti
  filter_upwards [hmaps, eventually_ge_atTop (N + m)] with n hn hnm
  have := hfinite n
  have := hfinite (n + 1)
  have heq : d n = d (n + 1) := by
    have h := (hm (n - N) (by omega)).symm.trans (hm (n + 1 - N) (by omega))
    simpa only [Nat.add_sub_of_le (by omega : N ≤ n),
      Nat.add_sub_of_le (by omega : N ≤ n + 1)] using h
  have hinj := (OrzechProperty.bijective_of_surjective_of_finrank_le (map n) hn heq.le).injective
  simp only [map, LinearMap.coe_comp, LinearEquiv.coe_coe, coe_cohomologyMapBaseLinear] at hinj
  -- Reassociate the three functions to cancel the source isomorphism first.
  rw [← Function.comp_assoc] at hinj
  exact (hinj.of_comp_right (src n).surjective).of_comp

/-- In a sequence of Cartier twists on a projective scheme, sections eventually lift
from the divisor if first cohomology of the restricted bundles eventually vanishes.
The isomorphisms identify each ideal-sheaf twist with the preceding bundle. -/
theorem eventually_surjective_pullbackSectionsLE_of_eventually_subsingleton_cohomology_quotient
    (k : Type u) [Field k] [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    (M : ℕ → InvertibleSheaf X) (e : ∀ n, (M (n + 1)).obj ⊗ I.sheaf ≅ (M n).obj)
    (hvan : ∀ᶠ n : ℕ in atTop,
      Subsingleton (Cohomology ((M n).obj ⊗ I.pushforwardSubscheme) 1)) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective
      (I.subschemeι.pullbackSectionsLE (M n).obj ⊤ ⊤ (by simp)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_injective_cohomologyMap_tensorIdeal k M e hvan)
  refine eventually_atTop.mpr ⟨N + 1, fun n hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact I.surjective_pullbackSectionsLE_of_injective_cohomologyMap _ (hN m (by omega))

variable {k : Type u} [Field k] [X.Over (Spec (.of k))] [hproj : X.IsProjectiveOver k]

local notation "L[" hI "]" => IsEffectiveCartier.toInvertibleSheaf hI
local notation "class(" L ")" => LineBundleClass.mk L

include hproj in
/-- Positive twists along an effective Cartier divisor with trivial conormal line
bundle eventually allow all sections on the divisor to lift. The cohomology
hypothesis concerns the original restriction. -/
theorem IsEffectiveCartier.eventually_surjective_pullbackSectionsLE_of_trivial_conormal
    (hI : I.IsEffectiveCartier) (L : InvertibleSheaf X)
    (htriv : LineBundleClass.pullback I.subschemeι (class(L[hI])) = 1)
    (hvan : Subsingleton (Cohomology (L.obj ⊗ I.pushforwardSubscheme) 1)) :
    ∀ᶠ n : ℕ in atTop, Function.Surjective (I.subschemeι.pullbackSectionsLE
      (L.tensorProduct (L[hI].dual.tensorPow n)).obj ⊤ ⊤ (by simp)) := by
  let M (n : ℕ) := L.tensorProduct (L[hI].dual.tensorPow n)
  have hm (n : ℕ) : class(M n) = class(L) * class(L[hI])⁻¹ ^ n := by
    simp only [M, mk_tensorProduct, mk_tensorPow, ← inv_mk]
  have hr (n : ℕ) : Subsingleton (Cohomology ((M n).obj ⊗ I.pushforwardSubscheme) 1) := by
    have he : class((InvertibleSheaf.pullback I.subschemeι).obj (M n)) =
        class((InvertibleSheaf.pullback I.subschemeι).obj L) := by
      simp only [← pullback_mk, hm, pullback_mul, pullback_pow, pullback_inv, htriv,
        inv_one, one_pow, mul_one]
    obtain ⟨e⟩ := mk_eq_mk_iff.mp he
    let e' := eqToIso (InvertibleSheaf.pullback_obj_obj I.subschemeι (M n)).symm ≪≫ e ≪≫
      eqToIso (InvertibleSheaf.pullback_obj_obj I.subschemeι L)
    let h := (I.cohomologyTensorRestrictionEquiv k (M n) 1).trans <|
      (cohomologyBaseLinearEquivOfIso k e' 1).trans (I.cohomologyTensorRestrictionEquiv k L 1).symm
    exact @Function.Injective.subsingleton _ _ _ h.injective hvan
  let e (n : ℕ) : (M (n + 1)).obj ⊗ I.sheaf ≅ (M n).obj :=
    hI.tensorProductTensorPowSuccIdealIso L n
  exact eventually_surjective_pullbackSectionsLE_of_eventually_subsingleton_cohomology_quotient
    k M e (Eventually.of_forall hr)

end AlgebraicGeometry.Scheme.IdealSheafData
