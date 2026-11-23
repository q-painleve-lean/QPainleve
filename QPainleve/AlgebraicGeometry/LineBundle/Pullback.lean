/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.LineBundle.Ratio
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange

/-!
# Pullback of line bundle frames

A section generating an invertible sheaf near a point pulls back to a
generator near every point over it. The section comparison uses the affine
base-change theorem for quasi-coherent modules.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
  [SheafOfModules.isInvertible Y M]

private theorem surjective_smul_pullbackSectionsLE {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (s : Γ(M, U))
    (hs : U ≤ M.nonvanishingLocus s) :
    Function.Surjective fun a : Γ(X, V) ↦ a • f.pullbackSectionsLE M U V hVU s := by
  let : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  let : Module Γ(Y, U) Γ((Modules.pullback f).obj M, V) :=
    Module.compHom _ (f.appLE U V hVU).hom
  let : IsScalarTower Γ(Y, U) Γ(X, V) Γ((Modules.pullback f).obj M, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ : Γ(M, U) →ₗ[Γ(Y, U)] Γ((Modules.pullback f).obj M, V) :=
    { toFun := f.pullbackSectionsLE M U V hVU
      map_add' := map_add _
      map_smul' := (f.pullbackSectionsLE M U V hVU).map_smulₛₗ }
  have hc := f.isBaseChange_pullbackSectionsLE M hU hV hVU (fun _ ↦ rfl) φ (fun _ ↦ rfl)
  let b := (Module.Basis.singleton Unit Γ(Y, U)).map (M.sectionFrame s hs)
  have hb : hc.basis b () = f.pullbackSectionsLE M U V hVU s := by
    rw [hc.basis_apply]
    simp [b, φ]
  intro t
  refine ⟨(hc.basis b).repr t (), ?_⟩
  simpa only [Fintype.sum_unique, hb] using (hc.basis b).sum_repr t

private theorem le_nonvanishingLocus_pullbackSections_of_isAffineOpen {U : Y.Opens}
    (hU : IsAffineOpen U)
    (s : Γ(M, U)) (hs : U ≤ M.nonvanishingLocus s) :
    f ⁻¹ᵁ U ≤ ((Modules.pullback f).obj M).nonvanishingLocus (f.pullbackSections M U s) := by
  let L := (Modules.pullback f).obj M
  intro x hx
  refine (Modules.mem_nonvanishingLocus_iff_of_mem hx).mpr
    ((Submodule.span_singleton_eq_top_iff _ _).mpr fun m ↦ ?_)
  obtain ⟨W, hxW, t, rfl⟩ := L.presheaf.exists_germ_eq m
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Opens.mem_inf.mpr ⟨hxW, hx⟩)
      (W ⊓ f ⁻¹ᵁ U).is_open'
  have hVU : V ≤ f ⁻¹ᵁ U := hVW.trans inf_le_right
  let j : V ⟶ W := homOfLE (hVW.trans inf_le_left)
  obtain ⟨a, ha⟩ := f.surjective_smul_pullbackSectionsLE M hU hV hVU s hs
    (L.presheaf.map j.op t)
  refine ⟨X.presheaf.germ V x hxV a, ?_⟩
  have h := congrArg (L.presheaf.germ V x hxV) ha
  dsimp only [L] at h
  simpa only [pullbackSectionsLE_apply, Modules.germ_smul,
    TopCat.Presheaf.germ_res_apply] using h

/-- A section pulls back to a generator over the inverse image of its nonvanishing locus. -/
theorem preimage_nonvanishingLocus_le {U : Y.Opens} (s : Γ(M, U)) :
    f ⁻¹ᵁ M.nonvanishingLocus s ≤
      ((Modules.pullback f).obj M).nonvanishingLocus (f.pullbackSections M U s) := by
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hV'⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx (M.nonvanishingLocus s).is_open'
  let i : V ⟶ U := homOfLE (hV'.trans (M.nonvanishingLocus_le s))
  have hframe := M.le_nonvanishingLocus_map i s hV'
  have h := f.le_nonvanishingLocus_pullbackSections_of_isAffineOpen M hV
    (M.presheaf.map i.op s) hframe
  rw [← f.pullbackSections_restrict M U i s, Modules.nonvanishingLocus_map] at h
  exact (h hxV).2

end AlgebraicGeometry.Scheme.Hom
