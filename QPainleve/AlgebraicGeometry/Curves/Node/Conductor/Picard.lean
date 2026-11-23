/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.Conductor
public import QPainleve.AlgebraicGeometry.IdealSheaf.Conductor.GluingUnit

import TauCeti.AlgebraicGeometry.Curves.Node.FiniteEtale
import TauCeti.AlgebraicGeometry.Curves.Node.Reduced
import TauCeti.AlgebraicGeometry.LineBundle.LocalRing

/-!
# The Picard kernel of the normalization of a nodal curve

For a nodal curve, line bundle classes trivialized by the blowup separating
the branches are classified by units on the branch scheme modulo rescalings on
the blowup and on the singular subscheme. This is the conductor description
underlying the product of branch ratios in [Gross, Hacking and Keel,
*Moduli of surfaces with an anti-canonical cycle*, Lemma 2.1](https://arxiv.org/abs/1211.6367v5).
-/

public noncomputable section

open CategoryTheory MonoidalCategory TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open Modules

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- Every line bundle on a nodal curve restricts trivially to its singular subscheme. -/
theorem pullback_singularLocus_subschemeι_eq_one
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)))
    (a : LineBundleClass X) :
    letI := hnodal.syntomic
    LineBundleClass.pullback (X.singularLocus k).subschemeι a = 1 := by
  let := hnodal.syntomic
  let I := X.singularLocus k
  have := X.etale_singularLocus_subschemeι_comp hnodal
  have : IsLocallyArtinian I.subscheme :=
    .of_locallyQuasiFinite (I.subschemeι ≫ (X ↘ Spec (.of k)))
  exact Subsingleton.elim _ _

private theorem inf_ker_pullback_singularLocus
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) :
    letI := hnodal.syntomic
    let I := X.singularLocus k
    (LineBundleClass.pullbackHom I.blowupToBase).ker ⊓
      (LineBundleClass.pullbackHom I.subschemeι).ker =
        (LineBundleClass.pullbackHom I.blowupToBase).ker := by
  let := hnodal.syntomic
  refine inf_eq_left.mpr fun a _ ↦ MonoidHom.mem_ker.mpr ?_
  rw [LineBundleClass.pullbackHom_apply]
  exact X.pullback_singularLocus_subschemeι_eq_one hnodal a

/-- Picard classes trivial on the normalization of a nodal curve correspond
multiplicatively to branch units modulo changes of the two conductor trivializations. -/
def nodalPicardKernelMulEquiv
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) :
    letI := hnodal.syntomic
    (LineBundleClass.pullbackHom (X.singularLocus k).blowupToBase).ker ≃*
      (Γ(X.branchScheme k, ⊤)ˣ ⧸
        ((X.branchSchemeToBlowup k).lineGluingCoboundary
          (X.branchSchemeToSingularLocus k)).range) := by
  let := hnodal.syntomic
  let I := X.singularLocus k
  have : IsFinite I.blowupToBase := X.isFinite_blowupToBase_singularLocus hnodal
  have : Surjective I.blowupToBase := X.surjective_blowupToBase_singularLocus hnodal
  have : IsReduced X := hnodal.isReduced
  have : IsSchemeTheoreticallyDominant I.blowupToBase := .of_isDominant _
  exact (MulEquiv.subgroupCongr (inf_ker_pullback_singularLocus hnodal).symm).trans
    ((X.isPullback_branchScheme k).flip.lineGluingClassMulEquiv
      ((IdealSheafData.ker_subschemeι I).trans
        (conductor_blowupToBase_singularLocus hnodal).symm))

/-- Compute the class of a line bundle in overlap coordinates using trivializations
on the normalization and the singular subscheme. -/
theorem nodalPicardKernelMulEquiv_apply
    (hnodal : AtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k))) :
    letI := hnodal.syntomic
    let I := X.singularLocus k
    ∀ (a : (LineBundleClass.pullbackHom I.blowupToBase).ker) (L : InvertibleSheaf X)
      (e : (pullback I.blowupToBase).obj L.obj ≅ 𝟙_ _)
      (d : (pullback I.subschemeι).obj L.obj ≅ 𝟙_ _),
      LineBundleClass.mk L = a.val →
        nodalPicardKernelMulEquiv hnodal a =
          QuotientGroup.mk
            ((X.isPullback_branchScheme k).flip.toCommSq.lineGluingUnit e d) := by
  let := hnodal.syntomic
  let I := X.singularLocus k
  have : IsFinite I.blowupToBase := X.isFinite_blowupToBase_singularLocus hnodal
  have : Surjective I.blowupToBase := X.surjective_blowupToBase_singularLocus hnodal
  have : IsReduced X := hnodal.isReduced
  have : IsSchemeTheoreticallyDominant I.blowupToBase := .of_isDominant _
  dsimp only
  intro a L e d hL
  rw [nodalPicardKernelMulEquiv, MulEquiv.trans_apply]
  exact (X.isPullback_branchScheme k).flip.lineGluingClassMulEquiv_apply _ _ L e d
    (hL.trans (MulEquiv.subgroupCongr_apply _ _).symm)

end AlgebraicGeometry.Scheme
