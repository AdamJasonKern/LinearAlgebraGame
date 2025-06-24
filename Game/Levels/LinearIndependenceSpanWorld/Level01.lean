import Game.Levels.VectorSpaceWorld.Level05

World "LinearIndependenceSpanWorld"
Level 1

Title "Linear Combinations"

Introduction "The first level of this world will introduce the definition of a linear combination. Let's
say we want to express that some vector `x` is a linear combination of some set `S ⊆ V`. This means
that there is some number of elements in `S`, that after some scalar multiplication, sums to `x`. We can
call this set of elements summing to `x` `s`, where `s : Finset V`, and `↑s ⊆ S`. We are using Finset
here, which means that `s` is a finite subset of V. This is because we can only sum in a way that makes
sense over a finite set. If `s` was infinite, there could be multiple ways of summing it to get different
answers., or a sum might not even exist. We also need to multiply every element of `s` by a scalar before
summing, whether that scalar be `1`, `0`, or anything else. We can represent this by a function `f : V → K`,
where each element of `s` gets mapped to the scalar we multiply by. Now, we are able to understand the
definition of linear combinations:

'''
def is_linear_combination (S : Set V) (x : V) : Prop :=
  ∃ (s : Finset V) (f : V → K), (↑s ⊆ S) ∧ (x = Finset.sum s (fun v => f v • v))
'''
"

Statement (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "You can either start using `{h}` or `{g}`."
  Branch
    rw [g]
    Hint "You should use `{h}` now."
    rw [h]
  rw [h]
  Hint "You should use `{g}` now."
  rw [g]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
