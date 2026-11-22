/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveOver
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import QPainleve.AlgebraicGeometry.ProjectiveSpectrum.AffineCover
import TauCeti.AlgebraicGeometry.Cohomology.ClosedImmersion.Basic
import TauCeti.AlgebraicGeometry.Cohomology.FiniteCover
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Basic
import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport

/-!
# Cohomology above the dimension of the support

On a projective scheme over an infinite field, a quasi-coherent sheaf of finite type
has no cohomology in degrees above the dimension of its support. The sheaf is the
direct image of its pullback to the closed subscheme defined by its annihilator.
The projective affine-cover bound then applies on that subscheme, including when
the annihilator defines a nonreduced structure. The proof uses Tau Ceti's
`isIso_unit_app_of_ker_ideal_le_annihilator`, `cohomologyPushforwardIso`, and
`subsingleton_cohomology_of_isAffineOpen_of_card_le`.

## References

* The Stacks Project, Proposition 20.20.7 (tag 02UZ), Grothendieck vanishing.
* The Stacks Project, Lemma 30.2.6 (tag 01XD), the comparison for affine covers.
-/

public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry (cohomologyPushforwardIso)

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Quasi-coherent cohomology on a projective scheme over an infinite field vanishes
above the dimension of the scheme, regardless of the dimension of the embedding. -/
theorem subsingleton_cohomology_of_projective_dim_lt {k : Type u} [Field k] [Infinite k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    (F : X.Modules) [F.IsQuasicoherent] {q : ℕ} (hdim : topologicalKrullDim X < q) :
    Subsingleton (Cohomology F q) := by
  classical
  obtain ⟨U, hU, hcover⟩ := X.exists_affineCover_of_dim_lt (k := k) hdim
  cases q with
  | zero =>
    have htop : (⊤ : X.Opens) = ⊥ := hcover.symm.trans (iSup_of_empty _)
    let A : TopCat.Sheaf AddCommGrpCat X :=
      (SheafOfModules.toSheaf X.ringCatSheaf).obj F
    have := AddCommGrpCat.subsingleton_of_isZero (Limits.isZero_zero AddCommGrpCat)
    have hsections := (A.isTerminalOfEqEmpty htop).uniqueUpToIso
      (Limits.isZero_zero AddCommGrpCat).isTerminal
    let : Subsingleton Γ(F, ⊤) := hsections.addCommGroupIsoToAddEquiv.toEquiv.subsingleton
    exact (cohomologyZeroEquiv F).toEquiv.subsingleton
  | succ q =>
    have : IsSeparated (terminal.from X) := by
      rw [← terminal.comp_from (X ↘ Spec (.of k))]
      infer_instance
    exact subsingleton_cohomology_of_isAffineOpen_of_card_le F Finset.univ_nonempty U
      (fun j _ ↦ hU j) (by simpa [Finset.sup_univ_eq_iSup] using hcover) (q + 1) (by simp)

/-- On a projective scheme over an infinite field, the cohomology of a quasi-coherent
module of finite type vanishes in every degree strictly greater than the Krull dimension
of the set of points with nonzero stalk. -/
theorem subsingleton_cohomology_of_support_dim_lt {k : Type u} [Field k] [Infinite k]
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [X.IsProjectiveOver k]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] {q : ℕ}
    (hdim : topologicalKrullDim ↥{x : X | Nontrivial (F.presheaf.stalk x)} < q) :
    Subsingleton (Cohomology F q) := by
  let hfinite (U : X.affineOpens) := F.finite_sections_of_isAffineOpen U.val U.property
  let I := F.annihilator hfinite
  let i := I.subschemeι
  let : I.subscheme.Over (Spec (.of k)) := ⟨i ≫ X ↘ Spec (.of k)⟩
  let : i.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : I.subscheme.IsProjectiveOver k := Scheme.IsProjectiveOver.of_isClosedImmersion k i
  have hsupport : Set.range i = {x : X | Nontrivial (F.presheaf.stalk x)} := by
    rw [I.range_subschemeι]
    ext x
    exact F.mem_support_annihilator_iff_nontrivial_stalk hfinite
  let e := i.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hsupport)
  have hdim' : topologicalKrullDim I.subscheme < q :=
    e.isHomeomorph.topologicalKrullDim_eq _ |>.trans_lt hdim
  have := isIso_unit_app_of_ker_ideal_le_annihilator i F fun U ↦ by
    rw [I.ker_subschemeι, F.annihilator_ideal hfinite]
  let G := (pullback i).obj F
  have : Subsingleton (Cohomology G q) :=
    subsingleton_cohomology_of_projective_dim_lt (k := k) G hdim'
  let iso := (cohomologyFunctor X q).mapIso
    (asIso ((pullbackPushforwardAdjunction i).unit.app F)) ≪≫ cohomologyPushforwardIso i G q
  exact iso.addCommGroupIsoToAddEquiv.toEquiv.subsingleton

end AlgebraicGeometry.Scheme.Modules
