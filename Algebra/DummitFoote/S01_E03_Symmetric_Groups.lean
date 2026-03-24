import Algebra.Prelude

open Function

universe u

variable {α : Type u}

-- "The permutations of {1, 2, 3, ..., n} are precisely the injective functions
-- of this set to itself because it is finite"
example [Finite α] {f : α → α} : Injective f → Bijective f
  := by --
  exact Finite.injective_iff_bijective.mp -- ∎
