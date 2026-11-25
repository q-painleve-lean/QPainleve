/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections

/-!
# Pullbacks of sections along equal composites

The canonical isomorphism between module pullbacks along two factorizations
of the same scheme morphism identifies their iterated pullbacks of sections.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {W X Y Z : Scheme.{u}} {f : W ⟶ X} {g : X ⟶ Z} {i : W ⟶ Y} {j : Y ⟶ Z}

/-- The canonical comparison between the two iterated module pullbacks along
equal composites of scheme morphisms. -/
noncomputable def pullbackCompIsoOfEq (h : f ≫ g = i ≫ j) (M : Z.Modules) :
    (pullback f).obj ((pullback g).obj M) ≅ (pullback i).obj ((pullback j).obj M) :=
  (pullbackComp f g).app M ≪≫ (pullbackCongr h).app M ≪≫ ((pullbackComp i j).app M).symm

/-- The comparison carries an iterated pullback of a section to its iterated
pullback along the other factorization, also on smaller opens. -/
theorem pullbackCompIsoOfEq_hom_app_pullbackSectionsLE
    (h : f ≫ g = i ≫ j) (M : Z.Modules) {U : Z.Opens} {V : X.Opens} {V' : Y.Opens}
    {O : W.Opens} (hV : V ≤ g ⁻¹ᵁ U) (hV' : V' ≤ j ⁻¹ᵁ U)
    (hO : O ≤ f ⁻¹ᵁ V) (hO' : O ≤ i ⁻¹ᵁ V') (s : Γ(M, U)) :
    (pullbackCompIsoOfEq h M).hom.app O
      (f.pullbackSectionsLE ((pullback g).obj M) V O hO (g.pullbackSectionsLE M U V hV s)) =
    i.pullbackSectionsLE ((pullback j).obj M) V' O hO' (j.pullbackSectionsLE M U V' hV' s) := by
  simp only [pullbackCompIsoOfEq, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Hom.comp_app, ConcreteCategory.comp_apply]
  rw [Scheme.Hom.pullbackSectionsLE_comp_hom, Scheme.Hom.pullbackSectionsLE_congr,
    Scheme.Hom.pullbackSectionsLE_comp j M U i V' hV' hO']

end AlgebraicGeometry.Scheme.Modules
