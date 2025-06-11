import Game.Metadata
import Game.Levels.VectorSpaceWorld.Level10

World "VectorSpaceWorld"
Level 12

Title "Vector Space World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."




/-- **Level 12: Monotonicity of Span**
If $A \subseteq B$ are sets of vectors, then `span A ⊆ span B`. In other words, a larger set of vectors can only have a larger (or equal) span. -/
theorem span_mono {A B : Set V} (hAB : A ⊆ B) : span A ⊆ span B := by
  intro x hxA
  -- x is in span A, so x is a linear combination of vectors from A.
  obtain ⟨s, f, hsA, hf0, rfl⟩ := hxA
  -- But A ⊆ B, so all vectors in s are also in B.
  have hsB : ↑s ⊆ B := hsA.trans hAB
  -- Thus, the same combination witnesses that x is in span B.
  exact ⟨s, f, hsB, hf0, rfl⟩

Conclusion "This last message appears if the level is solved."
