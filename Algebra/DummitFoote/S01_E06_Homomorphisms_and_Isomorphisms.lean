import Algebra.Prelude

open Function

universe u v

variable {G : Type u} {H : Type v}

-- "It is occasionally easy to see that two given groups are _not_ isomorphic.
-- For example, the exercises below assert that if φ : G → H is an isomorphism,
-- then, in particular,
--  (a) |G| = |H|,
--  (b) G is abelian if and only if H is abelian,
--  (c) for all x ∈ G, |x| = |φ(x)|.
-- "

section Part.A
variable [Group G] [Group H]

example [Fintype G] (φ : G ≃* H) : Fintype H := Fintype.ofEquiv G φ.toEquiv
example [Fintype H] (φ : G ≃* H) : Fintype G := Fintype.ofEquiv H φ.toEquiv.symm


-- Part (a): |G| = |H|
example [Fintype G] [Fintype H] (φ : G ≃* H)
  : Fintype.card G = Fintype.card H
  := by --
  exact Fintype.card_congr φ.toEquiv -- ∎

end Part.A

section Part.B

-- Part (b) G is abelian if and only if H is abelian.
@[reducible]
private def part_b [hG : CommGroup G] [Group H] (φ : G ≃* H) : CommGroup H := by
  exact MonoidHom.commGroupOfSurjective (G := G) φ φ.surjective

example [Group G] [CommGroup H] (φ : G ≃* H) : CommGroup G := part_b φ.symm

end Part.B

section Part.C
variable [Group G] [Group H]

-- Part (c) for all x ∈ G, |x| = |φ(x)|.
example {x : G} (φ : G ≃* H) : orderOf (φ x) = orderOf x := MulEquiv.orderOf_eq φ x
example {x : G} (φ : G ≃* H) : orderOf (φ x) = orderOf x
  := by --
  -- Mathlib's `MulEquiv.orderOf_eq` takes a vastly different approach. Very
  -- clean, I must say, and very well-integrated into the existing codebase.
  -- However, for educational purposes we shall try to solve this by reasoning
  -- available to us so far in Dummit & Foote.
  --
  -- Suppose first that there exists no positive n such that x ^ n = 1.
  -- Dummit & Foote denotes this as ∞ order, but in Mathlib we use order 0.
  if h₀ : orderOf x = 0 then
    rw [h₀]
    rw [orderOf_eq_zero_iff'] at h₀ ⊢
    -- We reduce to showing that (∀ n > 0, xⁿ ≠ 1) → (∀ n > 0, φ(x)ⁿ ≠ 1).
    -- To do this, we fix n and take the contrapositive: φ(x)ⁿ = 1 → xⁿ = 1.
    -- The final part can be deduced from the fact that φ(a) = 1 ↔ a = 1.
    intro n hn₀
    specialize h₀ n hn₀
    contrapose h₀
    rw [<-map_pow φ x n] at h₀
    rw [MulEquiv.map_eq_one_iff] at h₀
    exact h₀
  else
  -- So the trivial case is out of the way. Let n be the order of x. Then xⁿ = 1,
  -- from which we can show that φ(x)ⁿ = 1. This shows that the order of φ(x) is
  -- ≤ n. It then remains to show that the order of φ(x) is ≥ n, by showing that
  -- there is no m < n such that φ(x)ᵐ = 1.
  let n := orderOf x
  change orderOf (φ x) = n
  rw [orderOf_eq_iff (Nat.zero_lt_of_ne_zero h₀ : n > 0)]
  refine ⟨?_, ?_⟩
  · -- φ x ^ n = 1
    rw [<-map_pow φ x n, pow_orderOf_eq_one x]
    exact φ.map_one
  · -- ∀ m < n, 0 < m → φ x ^ m ≠ 1
    intro m hmn hm₀
    by_contra h'
    rw [<-map_pow φ x m, MulEquiv.map_eq_one_iff] at h'
    refine hmn.not_ge ?_
    exact orderOf_le_of_pow_eq_one hm₀ h' -- ∎

end Part.C
