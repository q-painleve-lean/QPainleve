/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Sections

/-!
# Tensor powers and nonvanishing loci

The bundled power of a line bundle has the underlying monoidal power used to form twists.
Positive powers of a section preserve its nonvanishing locus, allowing affine nonvanishing
covers whose sections have different degrees to be put in a common degree.
The comparison uses Tau Ceti's `tensorPowSuccIso` to append a factor to a monoidal power.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-- The underlying module of a bundled line bundle power is the monoidal tensor power. -/
def tensorPowObjIso (L : InvertibleSheaf X) (n : ℕ) :
    (L.tensorPow n).obj ≅ TauCeti.tensorPow L.obj n := by
  induction n with
  | zero =>
    rw [L.tensorPow_zero, TauCeti.tensorPow_zero]
    exact trivialObjIsoUnit X
  | succ n ih =>
    rw [L.tensorPow_succ]
    exact tensorProductObjIso _ _ ≪≫ whiskerRightIso ih L.obj ≪≫ TauCeti.tensorPowSuccIso L.obj n

end TauCeti.AlgebraicGeometry.InvertibleSheaf

namespace TauCeti.AlgebraicGeometry.SheafOfModules

variable {X : _root_.AlgebraicGeometry.Scheme.{u}}

/-- The monoidal tensor powers of an invertible module are invertible. -/
instance isInvertible_tensorPow (L : X.Modules) [isInvertible X L] (n : ℕ) :
    isInvertible X (TauCeti.tensorPow L n) :=
  (isInvertible X).prop_of_iso (InvertibleSheaf.tensorPowObjIso ⟨L, inferInstance⟩ n)
    (InvertibleSheaf.tensorPow ⟨L, inferInstance⟩ n).property

end TauCeti.AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

open TauCeti

variable {X : Scheme.{u}} {L : X.Modules}
  [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]

/-- Taking a positive tensor power of a section of an invertible sheaf preserves its
nonvanishing locus. -/
@[simp]
theorem nonvanishingLocus_tensorPowSection {U : X.Opens} (s : Γ(L, U)) {n : ℕ} (hn : 0 < n) :
    (tensorPow L n).nonvanishingLocus (tensorPowSection s n) = L.nonvanishingLocus s := by
  apply SetLike.ext
  intro x
  by_cases hx : x ∈ U
  · obtain ⟨V, t, hxV⟩ := exists_mem_trivialization L x
    let W := U ⊓ V
    let i : W ⟶ U := homOfLE inf_le_left
    let j : W ⟶ V := homOfLE inf_le_right
    let e := L.presheaf.map j.op (trivializationGenerator L t)
    have he : W ≤ L.nonvanishingLocus e := by
      simp [e, j.le]
    have hen : W ≤ (tensorPow L n).nonvanishingLocus (tensorPowSection e n) :=
      (le_nonvanishingLocus_iff _ (𝟙 W)).mpr fun A k ↦ by
        simpa using bijective_smul_tensorPowSection e
          ((le_nonvanishingLocus_iff e (𝟙 W)).mp he) n A k
    obtain ⟨f, hf⟩ := surjective_smul_of_le_nonvanishingLocus he (L.presheaf.map i.op s)
    have hs := basicOpen_eq_inf_nonvanishingLocus i s he hf
    have hsn := basicOpen_eq_inf_nonvanishingLocus i (tensorPowSection s n) hen
      (f := f ^ n) (by rw [map_tensorPowSection, ← hf, tensorPowSection_smul])
    rw [X.basicOpen_pow f hn, hs] at hsn
    have hxW : x ∈ W := ⟨hx, hxV⟩
    simpa only [Opens.mem_inf, hxW, true_and] using
      SetLike.ext_iff.mp hsn.symm x
  · exact iff_of_false (fun h ↦ hx (nonvanishingLocus_le _ h))
      (fun h ↦ hx (nonvanishingLocus_le _ h))

end AlgebraicGeometry.Scheme.Modules
