/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Morphisms of module sheaves from a basis

A compatible family of linear maps on a topological basis determines a morphism
of module sheaves. The underlying additive map is Mathlib's
`TopCat.Sheaf.restrictHomEquivHom`. Linearity can be checked on the same basis.
-/

public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type v} {B : ι → X.Opens}
  (hB : Opens.IsBasis (Set.range B))

section

variable (φ : ∀ i, Γ(M, B i) →ₗ[Γ(X, B i)] Γ(N, B i))
  (hφ : ∀ {i j} (f : B i ⟶ B j) (s : Γ(M, B j)),
    φ i (M.presheaf.map f.op s) = N.presheaf.map f.op (φ j s))

private def homOfBasisPresheaf : M.presheaf ⟶ N.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom _ ⟨_, N.isSheaf⟩ hB
    { app i := AddCommGrpCat.ofHom (φ i.unop).toAddMonoidHom
      naturality {_ _} f := ConcreteCategory.hom_ext _ _ (hφ f.unop.hom) }

private lemma homOfBasisPresheaf_app (i : ι) (x : Γ(M, B i)) :
    (homOfBasisPresheaf hB φ hφ).app (op (B i)) x = φ i x :=
  ConcreteCategory.congr_hom (TopCat.Sheaf.extend_hom_app _ _ hB _ i) x

private lemma homOfBasisPresheaf_smul (U : X.Opens) (r : Γ(X, U)) (x : Γ(M, U)) :
    (homOfBasisPresheaf hB φ hφ).app (op U) (r • x) =
      r • (homOfBasisPresheaf hB φ hφ).app (op U) x := by
  refine TopCat.Presheaf.IsSheaf.section_ext N.isSheaf fun x₀ hx₀ ↦ ?_
  obtain ⟨_, ⟨i, rfl⟩, hi, hiU⟩ := Opens.isBasis_iff_nbhd.mp hB hx₀
  refine ⟨B i, hiU, hi, ?_⟩
  simp only [N.map_smul, ← NatTrans.naturality_apply
    (homOfBasisPresheaf hB φ hφ) (homOfLE hiU).op, M.map_smul,
    homOfBasisPresheaf_app]
  exact (φ i).map_smul _ _

/-- Glue linear maps on a topological basis that commute with restriction. -/
def homOfBasis : M ⟶ N :=
  ⟨PresheafOfModules.homMk (homOfBasisPresheaf hB φ hφ)
    (fun U ↦ homOfBasisPresheaf_smul hB φ hφ U.unop)⟩

/-- The glued morphism evaluates to the specified linear map on each basis open. -/
@[simp]
theorem homOfBasis_app (i : ι) (x : Γ(M, B i)) :
    (homOfBasis hB φ hφ).app (B i) x = φ i x :=
  homOfBasisPresheaf_app hB φ hφ i x

end

include hB in
/-- Two morphisms of module sheaves agree if their sections maps agree on a topological basis. -/
theorem hom_ext_of_isBasis {f g : M ⟶ N}
    (h : ∀ i (x : Γ(M, B i)), f.app (B i) x = g.app (B i) x) : f = g := by
  apply (toPresheaf X).map_injective
  exact TopCat.Sheaf.hom_ext _ ⟨_, N.isSheaf⟩ hB
    (fun i ↦ ConcreteCategory.hom_ext _ _ (h i))

end AlgebraicGeometry.Scheme.Modules
