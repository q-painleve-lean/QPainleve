/-
Copyright (c) 2026 The QPainleve contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The QPainleve contributors
-/
module

public import QPainleve.AlgebraicGeometry.Curves.Node.CycleAction
public import TauCeti.AlgebraicGeometry.IdealSheaf.Over
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

import TauCeti.AlgebraicGeometry.IdealSheaf.BaseChange

/-!
# Pair isomorphisms with prescribed Picard and branch actions

The witness for signed period reconstruction is an isomorphism of the two boundary immersions
over a separably closed field. It records its Picard pullback and its action on the ordered
branches, which distinguishes the orientations even for cycles of length one or two.
-/

public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry
open Scheme (NodalCycleNumbering)

namespace QPainleve

universe u

variable {k : Type u} [Field k] [IsSepClosed k]

local notation "S(" k ")" => Spec (CommRingCat.of k)

variable {X Y : Scheme.{u}} [X.Over S(k)] [Y.Over S(k)]
  {D : X.IdealSheafData} {E : Y.IdealSheafData}
  [PrestableFamily (D.subscheme ↘ S(k))] [PrestableFamily (E.subscheme ↘ S(k))]
  {n : ℕ} [NeZero n] {α β : Type*}
  {p : α → (D.subscheme ↘ S(k)).smoothLocus} {q : β → (E.subscheme ↘ S(k)).smoothLocus}

/-- An isomorphism of pairs over the ground field realizing a prescribed Picard pullback
and a prescribed dihedral action on the numbered boundary cycles. -/
structure SignedTorelliPairIso
    (A : NodalCycleNumbering (k := k) (X := D.subscheme) p n)
    (C : NodalCycleNumbering (k := k) (X := E.subscheme) q n)
    (G : LineBundleClass Y → LineBundleClass X) (act : DihedralGroup n) where
  /-- The isomorphism of the boundary immersions over the ground field. -/
  pairIso : Arrow.mk (D.subschemeι.asOver S(k)) ≅ Arrow.mk (E.subschemeι.asOver S(k))
  /-- The pullback of a line bundle class is the prescribed Picard action. -/
  private pullback_right_eq (L : LineBundleClass Y) :
    LineBundleClass.pullback pairIso.hom.right.left L = G L
  /-- The isomorphism of boundaries induces the prescribed action on ordered branches. -/
  private boundaryCycleAction_left_eq :
    let b : D.subscheme ≅ E.subscheme := (Arrow.leftFunc ⋙ Over.forget S(k)).mapIso pairIso
    letI : b.hom.IsOver S(k) := ⟨Over.w pairIso.hom.left⟩
    b.boundaryCycleAction (k := k) A C = act

namespace SignedTorelliPairIso

variable {A : NodalCycleNumbering (k := k) (X := D.subscheme) p n}
  {C : NodalCycleNumbering (k := k) (X := E.subscheme) q n}
  {G : LineBundleClass Y → LineBundleClass X} {act : DihedralGroup n}

variable (e : SignedTorelliPairIso (D := D) (E := E) A C G act)

/-- The ambient surface isomorphism. -/
def surfaceIso : X ≅ Y := (Arrow.rightFunc ⋙ Over.forget S(k)).mapIso e.pairIso

/-- The isomorphism of the boundary subschemes. -/
def boundaryIso : D.subscheme ≅ E.subscheme :=
  (Arrow.leftFunc ⋙ Over.forget S(k)).mapIso e.pairIso

section

variable (a : X ≅ Y) [a.hom.IsOver S(k)] (b : D.subscheme ≅ E.subscheme) [b.hom.IsOver S(k)]
  (comm : b.hom ≫ E.subschemeι = D.subschemeι ≫ a.hom)
  (hPic : ∀ L : LineBundleClass Y, LineBundleClass.pullback a.hom L = G L)
  (hAction : b.boundaryCycleAction A C = act)

/-- Compatible ambient and boundary isomorphisms with the prescribed actions give a Torelli
pair isomorphism. -/
def ofIsos : SignedTorelliPairIso (D := D) (E := E) A C G act :=
  ⟨Arrow.isoMk' (D.subschemeι.asOver S(k)) (E.subschemeι.asOver S(k))
    (Over.isoMk b (comp_over b.hom S(k))) (Over.isoMk a (comp_over a.hom S(k)))
    (Over.OverMorphism.ext comm), hPic, hAction⟩

@[simp]
theorem surfaceIso_ofIsos : (ofIsos a b comm hPic hAction).surfaceIso = a :=
  Iso.ext rfl

@[simp]
theorem boundaryIso_ofIsos : (ofIsos a b comm hPic hAction).boundaryIso = b :=
  Iso.ext rfl

end

instance : e.surfaceIso.hom.IsOver S(k) := ⟨Over.w e.pairIso.hom.right⟩

instance : e.boundaryIso.hom.IsOver S(k) := ⟨Over.w e.pairIso.hom.left⟩

/-- The surface isomorphism induces the prescribed pullback on line bundle classes. -/
@[simp]
theorem pullback_eq (L : LineBundleClass Y) : LineBundleClass.pullback e.surfaceIso.hom L = G L :=
  e.pullback_right_eq L

/-- The boundary isomorphism induces the prescribed action on the numbered branches. -/
@[simp]
theorem boundaryCycleAction_eq : e.boundaryIso.boundaryCycleAction A C = act :=
  e.boundaryCycleAction_left_eq

/-- The boundary isomorphism commutes with the two boundary immersions. -/
@[reassoc]
theorem boundaryIso_hom_comp :
    e.boundaryIso.hom ≫ E.subschemeι = D.subschemeι ≫ e.surfaceIso.hom :=
  congrArg Over.Hom.left (Arrow.w e.pairIso.hom)

/-- The ambient isomorphism pulls back the target boundary ideal to the source boundary ideal. -/
@[simp]
theorem comap_surfaceIso_hom : E.comap e.surfaceIso.hom = D := by
  calc
    E.comap e.surfaceIso.hom = (e.boundaryIso.hom ≫ E.subschemeι).ker.comap e.surfaceIso.hom :=
      congrArg (·.comap e.surfaceIso.hom)
        ((Scheme.Hom.ker_comp_of_isIso _ _).trans E.ker_subschemeι).symm
    _ = D := by rw [e.boundaryIso_hom_comp, Scheme.Hom.comap_ker_comp_of_isClosedImmersion,
      D.ker_subschemeι]

/-- The ambient isomorphism determines the pair isomorphism by monicity of the
target boundary immersion. -/
@[ext]
theorem ext {e' : SignedTorelliPairIso (D := D) (E := E) A C G act}
    (h : e.surfaceIso.hom = e'.surfaceIso.hom) : e = e' := by
  have hb : e.boundaryIso.hom = e'.boundaryIso.hom :=
    (cancel_mono E.subschemeι).mp (e.boundaryIso_hom_comp.trans
      ((congrArg (D.subschemeι ≫ ·) h).trans e'.boundaryIso_hom_comp.symm))
  have he : e.pairIso = e'.pairIso := Iso.ext (Arrow.hom_ext _ _
    (Over.OverMorphism.ext hb) (Over.OverMorphism.ext h))
  cases e
  cases e'
  cases he
  rfl

end SignedTorelliPairIso

end QPainleve
