import Game.Metadata
import Game.Levels.VectorSpaceWorld.Level10
import Game.Levels.VectorSpaceWorld.Level13


World "VectorSpaceWorld"
Level 15

Title "SubsetSuperset"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/-- **Level 15: Independence of Subsets**


**Proposition 2.7(a):** Any subset of a linearly independent set is also linearly independent. -/
theorem subset_linear_independent [Field K] [AddCommGroup V][VectorSpace K V] {A B : Set V} (hBsubA : B ⊆ A) (hA : linear_independent K V A) :
    linear_independent K V B := by
  intros s f hsB sum_zero v hv
  -- Since s ⊆ B and B ⊆ A, we have s ⊆ A.
  have hsA : ↑s ⊆ A := hsB.trans hBsubA
  -- Now apply linear_independent A: all coefficients must be zero.
  exact hA s f hsA sum_zero v hv

/-- **Proposition 2.7(b):** If a set $A$ spans the whole space $V$, then any superset of $A$ also spans $V`. Adding more vectors can't reduce the span. -/
theorem superset_span_full {A B T: Set V} (hA : T = span K V A) (hAsubB : A ⊆ B) :
    T = span K V B := by
  -- `span A = T` means A is a spanning set for V (the entire space).
  -- We want to show `span B = V` as well.
  apply Set.eq_of_subset_of_subset
  -- First, show V ⊆ span B.**
  · -- Since span A = V and A ⊆ B, every vector in V (which is in span A) is also in span B by monotonicity.
    intros x hxV
    have : x ∈ span K V A := by rwa [← hA]  -- hxV : x ∈ V (trivially true for any x of type V)
    exact span_mono hAsubB this
  -- Second, show span B ⊆ V (this is always true, since V is the universe of discourse).**


  · rw [Set.subset_def]
    intro x hx
    rw [hA]

    -- Any x in span B is by definition an element of V (because B ⊆ V and sums of elements of V are in V).
     -- (x : V, so x ∈ V automatically)
