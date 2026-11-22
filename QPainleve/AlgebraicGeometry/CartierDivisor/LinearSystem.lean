/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import QPainleve.AlgebraicGeometry.CartierDivisor.ZeroDivisor
public import TauCeti.AlgebraicGeometry.CartierDivisor.Factorial
public import TauCeti.AlgebraicGeometry.WeilDivisor.LinearSystem.Basic

/-!
# Complete linear systems and projective sections

When all global functions are constants from the base field, the effective Cartier divisors
of a given line-bundle class are parametrized by lines in the space of global sections of
that bundle. On a locally factorial Noetherian integral scheme this identifies the native
complete linear system of a Weil divisor with the same projectivization.
-/

public section

open AlgebraicGeometry CategoryTheory
open Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

/-- Membership in a complete linear system is effectivity and equality of the associated
Cartier divisor classes in the Picard group. -/
theorem mem_completeLinearSystem_iff_cartier {D E : SchemeWeilDivisor X} :
    E ∈ (WeilDivisor.OrderSystem.ofScheme X).completeLinearSystem D ↔
      (equivCartierDivisorOfUniqueFactorizationMonoid E).IsEffective ∧
        (equivCartierDivisorOfUniqueFactorizationMonoid E).toLineBundleClass =
          (equivCartierDivisorOfUniqueFactorizationMonoid D).toLineBundleClass := by
  rw [(WeilDivisor.OrderSystem.ofScheme X).mem_completeLinearSystem_iff_divisorClass,
    isEffective_equivCartierDivisorOfUniqueFactorizationMonoid_iff]
  refine and_congr_right fun _ ↦ ?_
  rw [← (classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid X).injective.eq_iff,
    classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass,
    classGroupAddEquivLineBundleClassOfUniqueFactorizationMonoid_divisorClass]
  exact ⟨fun h ↦ (congrArg Additive.toMul h).symm, fun h ↦ congrArg Additive.ofMul h.symm⟩

end TauCeti.AlgebraicGeometry.SchemeWeilDivisor

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X] (L : InvertibleSheaf X)

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

attribute [local instance] sectionsBaseModule

private lemma zeroDivisor_eq_iff_projectivization_mk_eq
    (hconstants : Function.Surjective (baseRingToGlobalSections k X))
    {s t : Γ(L.obj, ⊤)} (hs : s ≠ 0) (ht : t ≠ 0) :
    L.zeroDivisor hs = L.zeroDivisor ht ↔
      Projectivization.mk k s hs = Projectivization.mk k t ht := by
  rw [L.zeroDivisor_eq_iff_exists_smul hs ht, Projectivization.mk_eq_mk_iff' k s t hs ht]
  have scalar (a : k) (v : Γ(L.obj, ⊤)) : a • v = baseRingToGlobalSections k X a • v := by
    -- Both module structures are restrictions of scalars on sections over the top open.
    change ((X.baseRingToStructurePresheaf k).app (.op ⊤)) a • v = _
    rw [Scheme.baseRingToStructurePresheaf_app_top, CommRingCat.ofHom_apply]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := hconstants a
    exact ⟨b, (scalar b t).trans (hb ▸ ha)⟩
  · rintro ⟨b, hb⟩
    have hne : b ≠ 0 := fun h ↦ hs (by simpa [h] using hb.symm)
    exact ⟨Units.map (baseRingToGlobalSections k X).toMonoidHom (Units.mk0 b hne),
      (scalar b t).symm.trans hb⟩

/-- Lines of global sections correspond to effective Cartier divisors of the given line-bundle
class, when every global function is a constant from the base field. -/
def projectivizationEquivEffectiveCartierDivisors
    (hconstants : Function.Surjective (baseRingToGlobalSections k X)) :
    Projectivization k Γ(L.obj, ⊤) ≃
      {D : Scheme.CartierDivisor X // D.IsEffective ∧ D.toLineBundleClass = LineBundleClass.mk L} :=
  Equiv.ofBijective
    (Projectivization.lift (fun s ↦
      ⟨L.zeroDivisor s.property, L.isEffective_zeroDivisor s.property,
        L.toLineBundleClass_zeroDivisor s.property⟩) (fun s t a h ↦ Subtype.ext <|
          (L.zeroDivisor_eq_iff_projectivization_mk_eq k hconstants s.property t.property).mpr
            ((Projectivization.mk_eq_mk_iff' k _ _ s.property t.property).mpr ⟨a, h.symm⟩)))
    (by
      constructor
      · intro p q
        induction p using Projectivization.ind with | h s hs =>
        induction q using Projectivization.ind with | h t ht =>
        intro h
        exact (L.zeroDivisor_eq_iff_projectivization_mk_eq k hconstants hs ht).mp
          (congrArg Subtype.val h)
      · rintro ⟨D, hD, hL⟩
        obtain ⟨s, hs, he⟩ := L.exists_zeroDivisor_eq hD hL
        exact ⟨Projectivization.mk k s hs, Subtype.ext he⟩)

/-- A projective section maps to its actual zero divisor. -/
@[simp]
lemma projectivizationEquivEffectiveCartierDivisors_mk
    (hconstants : Function.Surjective (baseRingToGlobalSections k X))
    (s : Γ(L.obj, ⊤)) (hs : s ≠ 0) :
    (L.projectivizationEquivEffectiveCartierDivisors k hconstants
      (Projectivization.mk k s hs)).val = L.zeroDivisor hs :=
  (rfl)

variable [IsNoetherian X] [∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)]

open SchemeWeilDivisor

/-- The complete linear system of a Weil divisor is the projectivization of the global sections
of any line bundle representing its Cartier class. -/
def completeLinearSystemEquivProjectivization
    (hconstants : Function.Surjective (baseRingToGlobalSections k X))
    (D : SchemeWeilDivisor X)
    (hL : (equivCartierDivisorOfUniqueFactorizationMonoid D).toLineBundleClass =
      LineBundleClass.mk L) :
    (WeilDivisor.OrderSystem.ofScheme X).completeLinearSystem D ≃
      Projectivization k Γ(L.obj, ⊤) :=
  (Equiv.subtypeEquiv equivCartierDivisorOfUniqueFactorizationMonoid.toEquiv
    (fun _ ↦ hL ▸ mem_completeLinearSystem_iff_cartier)).trans
    (L.projectivizationEquivEffectiveCartierDivisors k hconstants).symm

/-- In the complete linear system, a section represents its zero Weil divisor. -/
@[simp]
lemma completeLinearSystemEquivProjectivization_symm_mk
    (hconstants : Function.Surjective (baseRingToGlobalSections k X))
    (D : SchemeWeilDivisor X)
    (hL : (equivCartierDivisorOfUniqueFactorizationMonoid D).toLineBundleClass =
      LineBundleClass.mk L) (s : Γ(L.obj, ⊤)) (hs : s ≠ 0) :
    ((L.completeLinearSystemEquivProjectivization k hconstants D hL).symm
      (Projectivization.mk k s hs)).val = (L.zeroDivisor hs).toWeilDivisor := by
  rw [completeLinearSystemEquivProjectivization]
  exact equivCartierDivisorOfUniqueFactorizationMonoid_symm_apply _

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf
