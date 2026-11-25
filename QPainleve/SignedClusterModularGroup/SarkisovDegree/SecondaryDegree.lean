/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Blowup.Tower.Homaloidal

import QPainleve.AlgebraicGeometry.Blowup.Tower.PlaneResolution

/-!
# Secondary degree of a Sarkisov marking

The secondary degree of a birational map to the plane is the anticanonical
degree of its moving line class minus three. On any closed-point resolution
it is the sum of all base orders, including those at infinitely near centers.
This is the secondary degree used in the lexicographic descent in
[Lutz, Proposition 8.11][HKL].

[HKL]: https://arxiv.org/pdf/2005.05010v3#page=72
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry LineBundleClass Chow TauCeti.SymmetricAlgebra

universe u

namespace QPainleve

/-- The anticanonical degree of a moving line class minus the anticanonical
degree of a line in the target projective plane. -/
def sarkisovSecondaryDegree (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (L : LineBundleClass X) : ℤ :=
  -classIntersectionNumber k X L (mk (canonicalBundle k X 2)) - 3

/-- The secondary degree in terms of the intersection pairing and canonical class. -/
theorem sarkisovSecondaryDegree_def (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]
    (L : LineBundleClass X) :
    sarkisovSecondaryDegree k L =
      -classIntersectionNumber k X L (mk (canonicalBundle k X 2)) - 3 :=
  (rfl)

namespace BlowupTower.IsClosedPointTower

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {n : ℕ}
  {T : BlowupTower X n Y} [X.Over (Spec (.of k))] [X.IsProjectiveOver k] [IsIntegral X]
  [SmoothOfRelativeDimension 2 (X ↘ Spec (.of k))]

local notation "S" => Spec (CommRingCat.of k)
local notation "f" => (X ↘ S)
local notation "P" => Proj (homogeneousSubmodule k (Fin 3 → k))
local notation "H" => mk (Proj.symmetricAlgebraTwistingBundle k (Fin 3 → k) 1)

/-- In a resolution of a birational map to the plane the secondary degree
equals the sum of the successive base orders in total-transform coordinates. -/
theorem sarkisovSecondaryDegree_eq_sum (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    sarkisovSecondaryDegree k v.1.toMul = ∑ j, -v.2 j := by
  intro hNoeth v
  simpa only [sarkisovSecondaryDegree_def] using
    (hT.homaloidal_intersection_identities g hg hbir).2.symm

/-- The natural-valued secondary degree is the sum of the natural base orders.
The equality uses nonnegativity at every stage, so it also applies to towers
that contain extra blowups of order zero. -/
theorem toNat_sarkisovSecondaryDegree_eq_sum (hT : IsClosedPointTower X T)
    (g : Y ⟶ P) (hg : g ≫ (P ↘ S) = T.toBase ≫ f)
    (hbir : Scheme.BirationalOver g (𝟙 P)) :
    let : IsNoetherian X := isNoetherian_of_finiteType f
    let v := (T.picardMarking hT f).symm (Additive.ofMul (pullback g H))
    (sarkisovSecondaryDegree k v.1.toMul).toNat = ∑ j, (-v.2 j).toNat := by
  intro hNoeth v
  let := hNoeth
  have hdegree : sarkisovSecondaryDegree k v.1.toMul = ∑ j, -v.2 j :=
    hT.sarkisovSecondaryDegree_eq_sum g hg hbir
  obtain ⟨_, I, -, -, -, -, -, horders⟩ :=
    hT.exists_moving_base_ideal_of_plane_resolution g hg
  have horder j : -v.2 j = (hT.baseMultiplicities I j : ℤ) := horders j
  simp only [hdegree, horder, ← Nat.cast_sum, Int.toNat_natCast]

end BlowupTower.IsClosedPointTower

end QPainleve
