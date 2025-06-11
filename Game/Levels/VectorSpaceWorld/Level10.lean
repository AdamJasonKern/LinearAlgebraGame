import Game.Metadata
import Game.Levels.VectorSpaceWorld.Level09
--import Mathlib.Data.Set.Defs

World "VectorSpaceWorld"
Level 10

Title "Vector Space World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

/-- **Level 10: Span**
The **span** of a set $S$ is the set of all linear combinations of elements of $S`. It is the smallest subspace containing $S`. -/
def span (S : Set V) : Set V :=
  { x : V | is_linear_combination S x }

/-- Every element of $S$ lies in `span S` (since it can be expressed as a trivial linear combination of itself). -/
theorem mem_span_of_mem {S : Set V} {v : V} (hv : v ∈ S) : v ∈ span S := by
  -- By definition of span, we need to exhibit v as a linear combination of S.
  unfold span
  -- Use the result from Level 9: v is a linear combination of S.
  exact linear_combination_of_mem hv
