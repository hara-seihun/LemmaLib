/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Perm.Subgroup

/-!
# Two-closures of permutation groups

The two-closure of a permutation group consists of the permutations that agree with an element of
the group on each ordered pair. This file defines the two-closure as a subgroup and proves its basic
closure-operator properties.
-/

namespace Subgroup

variable {α : Type*}

/-- The two-closure of a permutation group. A permutation belongs to `twoClosure G` when, on every
ordered pair, it agrees with some element of `G`. -/
def twoClosure (G : Subgroup (Equiv.Perm α)) : Subgroup (Equiv.Perm α) where
  carrier := {q | ∀ x y, ∃ g ∈ G, g x = q x ∧ g y = q y}
  one_mem' := fun x y ↦ ⟨1, G.one_mem, by simp, by simp⟩
  mul_mem' := by
    intro q r hq hr x y
    obtain ⟨g, hg, hgx, hgy⟩ := hr x y
    obtain ⟨h, hh, hhx, hhy⟩ := hq (r x) (r y)
    refine ⟨h * g, G.mul_mem hh hg, ?_, ?_⟩
    · simpa [Equiv.Perm.mul_apply, hgx] using hhx
    · simpa [Equiv.Perm.mul_apply, hgy] using hhy
  inv_mem' := by
    intro q hq x y
    obtain ⟨g, hg, hgx, hgy⟩ := hq (q⁻¹ x) (q⁻¹ y)
    refine ⟨g⁻¹, G.inv_mem hg, ?_, ?_⟩
    · apply g.injective
      simpa using hgx.symm
    · apply g.injective
      simpa using hgy.symm

@[simp]
theorem mem_twoClosure {G : Subgroup (Equiv.Perm α)} {q : Equiv.Perm α} :
    q ∈ G.twoClosure ↔ ∀ x y, ∃ g ∈ G, g x = q x ∧ g y = q y :=
  Iff.rfl

/-- A permutation group is contained in its two-closure. -/
theorem le_twoClosure (G : Subgroup (Equiv.Perm α)) : G ≤ G.twoClosure := by
  intro g hg x y
  exact ⟨g, hg, rfl, rfl⟩

/-- Taking two-closures is monotone. -/
theorem twoClosure_mono : Monotone (twoClosure : Subgroup (Equiv.Perm α) →
    Subgroup (Equiv.Perm α)) := by
  intro G H hGH q hq x y
  obtain ⟨g, hg, hgx, hgy⟩ := hq x y
  exact ⟨g, hGH hg, hgx, hgy⟩

/-- Taking the two-closure twice has no further effect. -/
@[simp]
theorem twoClosure_twoClosure (G : Subgroup (Equiv.Perm α)) :
    G.twoClosure.twoClosure = G.twoClosure := by
  apply le_antisymm
  · intro q hq x y
    obtain ⟨h, hh, hhx, hhy⟩ := hq x y
    obtain ⟨g, hg, hgx, hgy⟩ := hh x y
    exact ⟨g, hg, hgx.trans hhx, hgy.trans hhy⟩
  · exact le_twoClosure G.twoClosure

/-- Membership in the two-closure is equivalent to preserving every binary relation that is
invariant under the original permutation group. -/
theorem mem_twoClosure_iff_preserves_invariant_binary_relations
    (G : Subgroup (Equiv.Perm α)) (q : Equiv.Perm α) :
    q ∈ G.twoClosure ↔
      ∀ R : Set (α × α),
        (∀ g ∈ G, ∀ x y, ((x, y) ∈ R ↔ (g x, g y) ∈ R)) →
          ∀ x y, ((x, y) ∈ R ↔ (q x, q y) ∈ R) := by
  constructor
  · intro hq R hR x y
    obtain ⟨g, hg, hgx, hgy⟩ := hq x y
    simpa [hgx, hgy] using hR g hg x y
  · intro hpres x y
    let R : Set (α × α) :=
      {z | ∃ g ∈ G, g x = z.1 ∧ g y = z.2}
    have hR : ∀ g ∈ G, ∀ u v,
        ((u, v) ∈ R ↔ (g u, g v) ∈ R) := by
      intro g hg u v
      constructor
      · rintro ⟨a, ha, hax, hay⟩
        refine ⟨g * a, G.mul_mem hg ha, ?_, ?_⟩
        · simp [Equiv.Perm.mul_apply, hax]
        · simp [Equiv.Perm.mul_apply, hay]
      · rintro ⟨a, ha, hax, hay⟩
        refine ⟨g⁻¹ * a, G.mul_mem (G.inv_mem hg) ha, ?_, ?_⟩
        · simpa [Equiv.Perm.mul_apply] using congrArg g.symm hax
        · simpa [Equiv.Perm.mul_apply] using congrArg g.symm hay
    have hxy : (x, y) ∈ R := ⟨1, G.one_mem, by simp, by simp⟩
    exact (hpres R hR x y).mp hxy

/-- The orbit of `x` under the stabilizer of `o` in a permutation group. -/
def pointStabilizerOrbit (G : Subgroup (Equiv.Perm α)) (o x : α) : Set α :=
  MulAction.orbit (MulAction.stabilizer G o) x

private theorem image_pointStabilizerOrbit_subset (G : Subgroup (Equiv.Perm α))
    {q : Equiv.Perm α} (hq : q ∈ G.twoClosure) {o : α} (hqo : q o = o) (x : α) :
    q '' G.pointStabilizerOrbit o x ⊆ G.pointStabilizerOrbit o x := by
  rintro _ ⟨z, hz, rfl⟩
  rw [pointStabilizerOrbit, MulAction.mem_orbit_iff] at hz ⊢
  obtain ⟨k, hk⟩ := hz
  obtain ⟨g, hg, hgo, hgz⟩ := hq o z
  have hgo' : (⟨g, hg⟩ : G) • o = o := by
    change g o = o
    exact hgo.trans hqo
  let g' : MulAction.stabilizer G o := ⟨⟨g, hg⟩, hgo'⟩
  refine ⟨g' * k, ?_⟩
  rw [mul_smul, hk]
  exact hgz

/-- An element of the two-closure that fixes `o` preserves every orbit of the point stabilizer of
`o`. -/
theorem image_pointStabilizerOrbit_eq (G : Subgroup (Equiv.Perm α)) {q : Equiv.Perm α}
    (hq : q ∈ G.twoClosure) {o : α} (hqo : q o = o) (x : α) :
    q '' G.pointStabilizerOrbit o x = G.pointStabilizerOrbit o x := by
  apply Set.Subset.antisymm (image_pointStabilizerOrbit_subset G hq hqo x)
  intro y hy
  have hqio : q⁻¹ o = o := by
    apply q.injective
    simp [hqo]
  have hInv := image_pointStabilizerOrbit_subset G (G.twoClosure.inv_mem hq) hqio x
  refine ⟨q⁻¹ y, hInv ⟨y, hy, rfl⟩, ?_⟩
  simp

end Subgroup
