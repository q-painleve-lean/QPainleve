/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import TauCeti.AlgebraicGeometry.Normalization.Finite
import TauCeti.AlgebraicGeometry.Morphisms.FiniteType
import TauCeti.RingTheory.UniversallyJapanese

/-!
# Finite normalization over a field

The normalization in the function field of an integral scheme locally of finite type over a
field is finite. The affine criterion
`TauCeti.AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint_iff` reduces
this to the fact that domains of finite type over a field are Japanese.
-/

public section

open CategoryTheory TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Normalization in the function field of an integral scheme locally of finite type over a
field is finite. -/
theorem isFinite_fromNormalization_fromSpecStalk_genericPoint_of_locallyOfFiniteType
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  apply isFinite_fromNormalization_fromSpecStalk_genericPoint_iff.mpr
  intro U hU hne
  let : Nonempty U := hne
  let : Algebra k Γ(Y, U) :=
    (((p.appLE ⊤ U le_top).hom).comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) := p.finiteType_ΓSpecIso_inv_comp_appLE hU
  let : TauCeti.Ring.IsJapanese Γ(Y, U) :=
    TauCeti.Ring.IsUniversallyJapanese.isJapanese k _
  infer_instance

end AlgebraicGeometry.Scheme.Hom
