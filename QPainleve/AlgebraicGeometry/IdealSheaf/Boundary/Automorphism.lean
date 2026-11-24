/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor.FixedBranches
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.Scheme.CodimensionOnePoint

/-!
# The Picard kernel fixing the components and branches of a nodal boundary

This subgroup is intrinsic to the pair over the ground field. Fixing the
boundary components and fixing its branches are separate conditions. In
particular, an automorphism fixing the sole component of a self-nodal boundary
can exchange the two branches.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry LineBundleClass

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (D : X.IdealSheafData)
  {f : X ⟶ Spec (.of k)} (hN : AtWorstNodalOfRelativeDimensionOne (D.subschemeι ≫ f))

/-- Automorphisms over the field which act trivially on the Picard group, fix every
prime boundary component, and restrict to a branch-fixing boundary automorphism. -/
def picardNodalBoundaryAut : Subgroup (Aut X) where
  carrier := {a | ∃ ha : a.asIso.hom ≫ f = f,
    (∀ L, pullback a.asIso.hom L = L) ∧
    (∀ x : CodimensionOnePoint X, x.val ∈ D.support → a.asIso.hom x.val = x.val) ∧
    ∃ (d : D.subscheme ≅ D.subscheme) (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ a.asIso.hom),
      d.FixesNodalBranches _ hN (by rw [reassoc_of% hd, ha])}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Aut.one_asIso, Iso.refl_hom, Category.id_comp, pullback_id,
      Scheme.Hom.id_base, TopCat.coe_id, id_eq, implies_true, true_and]
    exact ⟨trivial, Iso.refl _, by simp, Iso.fixesNodalBranches_refl hN⟩
  mul_mem' := by
    rintro a b ⟨ha, hPa, hCa, d, hd, hBd⟩ ⟨hb, hPb, hCb, e, he, hBe⟩
    simp only [Set.mem_ofPred_eq, Aut.mul_asIso, Iso.trans_hom]
    refine ⟨by rw [Category.assoc, ha, hb], fun L ↦ by rw [← pullback_comp, hPa, hPb],
      fun x hx ↦ by rw [Scheme.Hom.comp_apply, hCb x hx, hCa x hx], e ≪≫ d, ?_, hBe.trans hBd⟩
    rw [Iso.trans_hom, Category.assoc, hd, reassoc_of% he]
  inv_mem' := by
    rintro a ⟨ha, hPa, hCa, d, hd, hBd⟩
    simp only [Set.mem_ofPred_eq, Aut.inv_asIso, Iso.symm_hom]
    refine ⟨by rw [← ha, Iso.inv_hom_id_assoc, ha], ?_, ?_, d.symm, ?_, hBd.symm⟩
    · intro L
      rw [← hPa L, pullback_comp, Iso.inv_hom_id, pullback_id, hPa]
    · intro x hx
      have h := congrArg a.asIso.inv (hCa x hx)
      simpa only [← Scheme.Hom.comp_apply, Iso.hom_inv_id, Scheme.Hom.id_base, TopCat.coe_id,
        id_eq] using h.symm
    · rw [Iso.symm_hom, ← cancel_mono a.asIso.hom, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, ← hd, Iso.inv_hom_id_assoc]

/-- Membership in the Picard kernel with fixed boundary components and branches. -/
theorem mem_picardNodalBoundaryAut {a : Aut X} :
    a ∈ D.picardNodalBoundaryAut hN ↔ ∃ ha : a.asIso.hom ≫ f = f,
      (∀ L, pullback a.asIso.hom L = L) ∧
      (∀ x : CodimensionOnePoint X, x.val ∈ D.support → a.asIso.hom x.val = x.val) ∧
      ∃ (d : D.subscheme ≅ D.subscheme) (hd : d.hom ≫ D.subschemeι = D.subschemeι ≫ a.asIso.hom),
        d.FixesNodalBranches _ hN (by rw [reassoc_of% hd, ha]) :=
  (Iff.rfl)

end AlgebraicGeometry.Scheme.IdealSheafData
