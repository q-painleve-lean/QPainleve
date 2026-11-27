/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.Geometry.Toric.Fan.Evaluation

import QPainleve.AlgebraicGeometry.RationalMap.Composition.Basic

/-!
# Fixed-center evaluation under translated fan equivalences

An isomorphism consisting of a fan equivalence and a torus translation
intertwines Laurent-coordinate evaluation with the matching label map.
Each center parameter is rescaled by the inverse of its charge character
at the translating point.
-/

public section

open AlgebraicGeometry CategoryTheory Module Multiplicative
open TauCeti.LaurentRing

namespace TauCeti.Toric.FanEquiv

universe u

variable (R : Type u) [CommRing R] [IsDomain R] {N N' : Type u} {V V' : Type*}
  [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Φ : Fan i} {Ψ : Fan i'}
  [Nonempty Φ.cones] [Nonempty Ψ.cones]
  {ι κ : Type u} [DecidableEq ι] [DecidableEq κ]

/-- Pullback through a fan equivalence followed by a translation relabels the fixed-center
X evaluation. The target center of each label is multiplied back by the value of its
charge character at the translating point. The map `e` sends target labels to source labels. -/
theorem comp_xEvaluation_of_toric_iso (f : FanEquiv Φ Ψ)
    [Finite ι] [Finite κ] (b : Module.Basis (Fin 2) ℤ N) (b' : Module.Basis (Fin 2) ℤ N')
    (s : ι → Φ.Ray) (t : κ → Ψ.Ray) (e : κ → ι)
    (c : Multiplicative (ι → ℤ) →* Rˣ) (d : Multiplicative (κ → ℤ) →* Rˣ)
    (χ : Multiplicative (N' →+ ℤ) →* Rˣ)
    (hray : ∀ j, f.rayEquiv (s (e j)) = t j)
    (hdet : ∀ x y, b'.detDualEquiv (f.latticeEquiv x) (f.latticeEquiv y) = b.detDualEquiv x y)
    (hc : ∀ j, d (ofAdd (Pi.single j 1)) *
      χ (ofAdd (b'.detDualEquiv (t j).primitiveGenerator).toAddMonoidHom) =
        c (ofAdd (Pi.single (e j) 1))) :
    ((f.toFanHom.finiteFanSchemeHom R) ≫ (Ψ.torusTranslationIso R χ).hom).toRationalMap.comp
      (Ψ.xEvaluation R b' t d) =
      (Φ.xEvaluation R b s c).compHom
        (Spec.map (CommRingCat.ofHom (rename (R := R) e).toRingHom)) := by
  let charge := ((addMonoidHomLequivInt ℤ).symm.toLinearMap.comp
    (b'.detDualEquiv.toLinearMap.comp (Fan.rayChargeMap t))).toAddMonoidHom
  let d₀ := d * χ.comp charge.toMultiplicative
  have hd : d₀ / χ.comp charge.toMultiplicative = d := by
    ext x
    simp [d₀]
  have htranslate := Ψ.torusTranslation_comp_xEvaluation R b' t d₀ χ
  dsimp only at htranslate
  rw [hd] at htranslate
  have hcomp :
      ((f.toFanHom.finiteFanSchemeHom R) ≫ (Ψ.torusTranslationIso R χ).hom).toRationalMap.comp
        (Ψ.xEvaluation R b' t d) =
      (f.toFanHom.finiteFanSchemeHom R).toRationalMap.comp (Ψ.xEvaluation R b' t d₀) := by
    simp only [← htranslate, ← Scheme.RationalMap.comp_assoc, Scheme.RationalMap.comp_toRationalMap,
      Scheme.Hom.toRationalMap_compHom]
  rw [hcomp]
  apply f.toFanHom.comp_xEvaluation R
  · intro j
    simpa only [d₀, MonoidHom.mul_apply, MonoidHom.comp_apply, charge,
      AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd,
      LinearMap.toAddMonoidHom_coe, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Fan.rayChargeMap_single, addMonoidHomLequivInt_symm_apply] using hc j
  · intro j
    rw [← hray j, primitiveGenerator_rayEquiv]
    ext x
    simpa only [toFanHom_latticeMap, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe,
      Function.comp_apply, AddMonoidHom.coe_ofClass] using hdet (s (e j)).primitiveGenerator x

end TauCeti.Toric.FanEquiv
