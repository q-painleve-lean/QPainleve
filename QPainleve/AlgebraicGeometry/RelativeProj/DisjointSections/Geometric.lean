/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.RelativeProj.DisjointSections.Basic

import QPainleve.AlgebraicGeometry.RelativeProj.LineBundle.Section

/-!
# Splitting a projective bundle along geometric sections

Two disjoint sections of the projectivization of a rank-two bundle give a splitting
into the restrictions of its first twist to those sections. This identifies the
original sections with the two summand quotients and works over an arbitrary base.
We use the quotient convention of [Stacks, Section 27.21][Stacks].

[Stacks]: https://stacks.math.columbia.edu/tag/01OA
-/

public section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme.Modules

universe u

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

variable {X : Scheme.{u}} (E : FixedRank X 2)

local notation "F[" V "]" =>
  Functor.obj (FiniteLocallyFreeSheaf.toQuasicoherent X) (ObjectProperty.FullSubcategory.obj V)
local notation "A[" F "]" =>
  ObjectProperty.FullSubcategory.obj (Functor.obj (gradedSymmetricAlgebra X) F)
local notation "P" => CommMon.relativeProj A[F[E]]
local notation "p" => CommMon.relativeProjToBase A[F[E]]
local notation "T" => CommMon.relativeProjTwistingSheaf A[F[E]] 1

/-- Disjoint sections of a rank-two projective bundle give two line quotients inducing
an isomorphism to their direct sum. Each quotient may be taken with any target line
bundle identified with the tautological twist restricted to the corresponding section. -/
theorem exists_split_projective_bundle_iso_of_disjoint_sections
    (s t : X ⟶ P) (hs : s ≫ p = 𝟙 X) (ht : t ≫ p = 𝟙 X)
    (hd : Disjoint (Set.range s) (Set.range t))
    (L M : FixedRank X 1)
    (e : (Scheme.Modules.pullback s).obj T ≅ L.obj.obj)
    (f : (Scheme.Modules.pullback t).obj T ≅ M.obj.obj) :
    ∃ (q : F[E] ⟶ F[L]) (r : F[E] ⟶ F[M]) (hq : Epi q.hom) (hr : Epi r.hom),
      letI := hq
      letI := hr
      IsIso (biprod.lift q r) ∧
        L.relativeProjSectionOfQuotient q = s ∧ M.relativeProjSectionOfQuotient r = t := by
  obtain ⟨q, hq, hqs⟩ := L.exists_relativeProjLineQuotient_of_section (F := F[E]) s hs e
  obtain ⟨r, hr, hrt⟩ := M.exists_relativeProjLineQuotient_of_section (F := F[E]) t ht f
  let := hq
  let := hr
  exact ⟨q, r, hq, hr, E.isIso_biprod_lift_of_disjoint_quotient_sections L M q r
    (by simpa only [hqs, hrt] using hd), hqs, hrt⟩

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank
