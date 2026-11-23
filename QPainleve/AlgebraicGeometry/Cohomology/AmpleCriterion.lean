/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.Cohomology.Basic

import QPainleve.AlgebraicGeometry.IdealSheaf.ResidueField
import QPainleve.AlgebraicGeometry.IdealSheaf.Tensor.Restriction
import QPainleve.AlgebraicGeometry.LineBundle.Pullback
import QPainleve.AlgebraicGeometry.LineBundle.TensorProduct
import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
import TauCeti.AlgebraicGeometry.Modules.Tensor.Sections

/-!
# A cohomological criterion for ampleness

On a scheme carrying an ample line bundle, first cohomology of twists by the
ideals of closed points controls ampleness. A section lifted at a closed point
can be multiplied by a section of a reference ample line bundle, so that its
nonvanishing locus is affine. Compare the closed-point argument of
[Stacks Project, Lemma 30.3.3](https://stacks.math.columbia.edu/tag/0B5P).
-/

public section

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.LineBundleClass

open _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

private theorem exists_section_at_closedPoint (M : InvertibleSheaf X)
    (x : X) (hx : IsClosed ({x} : Set X))
    (hvan : Subsingleton (Cohomology (M.obj ⊗ (X.fromSpecResidueField x).ker.sheaf) 1)) :
    ∃ z : Γ(M.obj, ⊤), x ∈ M.obj.nonvanishingLocus z := by
  let i := X.fromSpecResidueField x
  let I := i.ker
  have : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hx
  have : IsAffine I.subscheme := IsAffine.of_isIso (asIso i.toImage).inv
  let y : I.subscheme := ⟨x, by
    rw [← SetLike.mem_coe]
    exact (Scheme.support_ker_fromSpecResidueField_of_isClosed hx).symm ▸ Set.mem_singleton x⟩
  let N := (InvertibleSheaf.pullback I.subschemeι).obj M
  obtain ⟨t, ht⟩ := InvertibleSheaf.isGloballyGenerated_iff.mp
    N.isGloballyGenerated_of_isAffine y
  let e := eqToIso (InvertibleSheaf.pullback_obj_obj I.subschemeι M)
  have htop : (⊤ : I.subscheme.Opens) ≤ I.subschemeι ⁻¹ᵁ (⊤ : X.Opens) :=
    I.subschemeι.preimage_top.ge
  let j := homOfLE htop
  have : IsIso j := by
    have heq : (⊤ : I.subscheme.Opens) = I.subschemeι ⁻¹ᵁ (⊤ : X.Opens) := by simp
    exact (show IsIso (eqToHom heq) from inferInstance)
  obtain ⟨t', ht'⟩ := (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback I.subschemeι).obj M.obj).presheaf.map j.op)).2 (e.hom.app ⊤ t)
  have := I.isIso_tensorRestrictionHom M
  obtain ⟨q, hq⟩ := (ConcreteCategory.bijective_of_isIso
    ((I.tensorRestrictionHom M).app ⊤)).2 t'
  obtain ⟨z, hz⟩ := I.surjective_tensorRestriction_of_subsingleton_cohomology_one M.obj hvan q
  have hcomp : ((ρ_ M.obj).inv ≫ M.obj ◁ I.toPushforwardSubscheme) ≫
      I.tensorRestrictionHom M = (pullbackPushforwardAdjunction I.subschemeι).unit.app M.obj := by
    rw [Category.assoc, I.tensorRestrictionHom_unit]
  have hunit := ConcreteCategory.congr_hom
    (congrArg (fun g ↦ _root_.AlgebraicGeometry.Scheme.Modules.Hom.app g ⊤) hcomp) z
  rw [Hom.comp_app, ConcreteCategory.comp_apply, hz, hq] at hunit
  have hres : I.subschemeι.pullbackSectionsLE M.obj ⊤ ⊤ htop z = e.hom.app ⊤ t := by
    rw [Scheme.Hom.pullbackSectionsLE_apply, Scheme.Hom.pullbackSections_apply, ← hunit]
    exact ht'
  refine ⟨z, ?_⟩
  have hy : I.subschemeι y = x := I.subschemeι_apply y
  rw [← hy, ← Scheme.Hom.mem_preimage,
    ← top_inf_eq (I.subschemeι ⁻¹ᵁ M.obj.nonvanishingLocus z),
    ← nonvanishingLocus_pullbackSectionsLE M.obj I.subschemeι htop z,
    hres, nonvanishingLocus_hom_app]
  exact ht

/-- On a scheme carrying an ample class, a line bundle is ample if, after
tensoring by any fixed line bundle, some positive power has vanishing first
cohomology with the ideal of any prescribed closed point. -/
theorem isAmple_mk_of_subsingleton_cohomology_one_closedPoint (L : InvertibleSheaf X)
    {a : LineBundleClass X} (ha : a.IsAmple)
    (hvan : ∀ (x : X), IsClosed ({x} : Set X) → ∀ P : InvertibleSheaf X,
      ∃ n : ℕ, 0 < n ∧
        Subsingleton (Cohomology ((P.tensorProduct (L.tensorPow n)).obj ⊗
          (X.fromSpecResidueField x).ker.sheaf) 1)) :
    (mk L).IsAmple := by
  let := ha.compactSpace
  rw [isAmple_iff_forall_isClosed_singleton]
  intro x hx
  obtain ⟨m, -, A, -, s, hs, hU⟩ := ha.exists_isAffineOpen_nonvanishingLocus x
  obtain ⟨n, hn, hcoh⟩ := hvan x hx A.dual
  let M := A.dual.tensorProduct (L.tensorPow n)
  obtain ⟨z, hz⟩ := exists_section_at_closedPoint M x hx hcoh
  let B := A.tensorProduct M
  let u := (A.tensorProductObjIso M).inv.app ⊤ (tmulRight A.obj z s)
  have hu : B.obj.nonvanishingLocus u = A.obj.nonvanishingLocus s ⊓ M.obj.nonvanishingLocus z :=
    (nonvanishingLocus_hom_app (A.tensorProductObjIso M).symm _).trans
      (nonvanishingLocus_tmulRight s z)
  refine ⟨n, hn, B, ?_, u, hu ▸ ⟨hs, hz⟩, ?_⟩
  · simp [B, M, mk_tensorProduct, mk_tensorPow, ← inv_mk, ← mul_assoc]
  · rw [hu, ← nonvanishingLocus_map (A.obj.nonvanishingLocus s).leTop]
    exact hU.nonvanishingLocus _

end TauCeti.AlgebraicGeometry.LineBundleClass
