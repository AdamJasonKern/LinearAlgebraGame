import Game.Metadata
import Game.Levels.VectorSpaceWorld.Level12

World "VectorSpaceWorld"
Level 13

Title "Vector Space World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]


/-- **Level 13: Linear Independence**
A set of vectors $S$ is **linearly independent** if no vector in $S$ can be written as a linear combination of the others. Equivalently, the only solution to a linear combination of elements of $S$ equaling zero is the trivial solution (all coefficients zero). Here we formalize this condition. -/

def linear_independent [Field K] [AddCommGroup V][VectorSpace K V] (S : Set V) : Prop :=
  ∀ (s : Finset V) (f : V → K),
    (↑s ⊆ S) → (Finset.sum s (fun v ↦ f v • v) = 0) → (∀ v ∈ s, f v = 0)
