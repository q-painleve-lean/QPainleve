/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Monoidal
public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Sections
import QPainleve.AlgebraicGeometry.LineBundle.Frame

/-!
# Nonvanishing of tensor products of sections

The nonvanishing locus of a pure tensor of two line bundle sections is the
intersection of their nonvanishing loci.
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry.SheafOfModules

/-- The tensor product of two invertible modules is invertible. -/
instance isInvertible_tensor {X : Scheme.{u}} (M L : X.Modules)
    [isInvertible X M] [isInvertible X L] : isInvertible X (M ⊗ L) :=
  CategoryTheory.ObjectProperty.prop_tensor
    (P₁ := isInvertible X) (P₂ := isInvertible X) inferInstance inferInstance

end TauCeti.AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} {M L : X.Modules}
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X M]
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]

/-- A pure tensor of line bundle sections generates precisely where both sections generate. -/
@[simp]
theorem nonvanishingLocus_tmulRight {U : X.Opens} (s : Γ(M, U)) (t : Γ(L, U)) :
    (M ⊗ L).nonvanishingLocus (tmulRight M t s) =
      M.nonvanishingLocus s ⊓ L.nonvanishingLocus t := by
  apply SetLike.ext
  intro x
  by_cases hx : x ∈ U
  · obtain ⟨V, v, hxV⟩ := M.exists_mem_trivialization x
    obtain ⟨W, w, hxW⟩ := L.exists_mem_trivialization x
    let A := U ⊓ (V ⊓ W)
    let i : A ⟶ U := homOfLE inf_le_left
    let j : A ⟶ V := homOfLE (inf_le_right.trans inf_le_left)
    let k : A ⟶ W := homOfLE (inf_le_right.trans inf_le_right)
    let e := M.presheaf.map j.op (M.trivializationGenerator v)
    let f := L.presheaf.map k.op (L.trivializationGenerator w)
    have he : A ≤ M.nonvanishingLocus e := by simp [e, j.le]
    have hf : A ≤ L.nonvanishingLocus f := by simp [f, k.le]
    have hef : A ≤ (M ⊗ L).nonvanishingLocus (tmulRight M f e) := by
      refine (le_nonvanishingLocus_iff _ (𝟙 A)).mpr fun B b ↦ ?_
      rw [Category.comp_id, map_tmulRight]
      simpa only [Category.comp_id, Function.comp_def, LinearMap.map_smul] using
        (bijective_tmulRight_of_le_nonvanishingLocus M (L.presheaf.map b.op f)
          (by rw [nonvanishingLocus_map]; exact le_inf le_rfl (b.le.trans hf))).comp
          ((le_nonvanishingLocus_iff e (𝟙 A)).mp he B b)
    obtain ⟨a, ha⟩ := M.surjective_smul_of_le_nonvanishingLocus he (M.presheaf.map i.op s)
    obtain ⟨b, hb⟩ := L.surjective_smul_of_le_nonvanishingLocus hf (L.presheaf.map i.op t)
    have hab : (a * b) • tmulRight M f e =
        (M ⊗ L).presheaf.map i.op (tmulRight M t s) := by
      rw [map_tmulRight, ← ha, ← hb, tmulRight_smul, LinearMap.map_smul, smul_smul, mul_comm]
    have h := (M ⊗ L).basicOpen_eq_inf_nonvanishingLocus i _ hef hab
    rw [X.basicOpen_mul, M.basicOpen_eq_inf_nonvanishingLocus i s he ha,
      L.basicOpen_eq_inf_nonvanishingLocus i t hf hb] at h
    have hxA : x ∈ A := ⟨hx, hxV, hxW⟩
    simpa only [Opens.mem_inf, hxA, true_and] using SetLike.ext_iff.mp h.symm x
  · exact iff_of_false (fun h ↦ hx (nonvanishingLocus_le _ h))
      (fun h ↦ hx (nonvanishingLocus_le _ h.1))

end AlgebraicGeometry.Scheme.Modules
