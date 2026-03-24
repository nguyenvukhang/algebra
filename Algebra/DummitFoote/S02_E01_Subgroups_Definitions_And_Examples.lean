import Algebra.Prelude

universe u

variable {G : Type u} [Group G]

-- Subgroups in Lean are a `structure` (like C structs). They have a `.carrier`
-- which is the set of elements, and then there are conditions upon this set.
example : Subgroup G := Subgroup.center G

-- The trivial subgroup.
example : Subgroup G := ⊥
example : (⊥ : Subgroup G).carrier = {1} := rfl

-- The whole group is a subgroup of itself, of course.
example : Subgroup G := ⊤
example : (⊤ : Subgroup G).carrier = Set.univ := rfl
