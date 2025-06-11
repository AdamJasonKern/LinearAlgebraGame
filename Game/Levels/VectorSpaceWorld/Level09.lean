--import Mathlib.Data.Set.Basic
import Game.Metadata
import Game.Levels.VectorSpaceWorld.Level01


World "VectorSpaceWorld"
Level 9

Title "Vector Space World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

variable (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V]
#check Set.singleton_subset_iff
/-- **Level 9: Linear Combination**
A vector $x$ is called a **linear combination** of a set $S$ if it can be expressed as a finite sum of elements of $S$ scaled by scalars in the field. Here we formalize this concept. ∑ v in s, f v • v-/
def is_linear_combination (S : Set V) (x : V) : Prop :=
  ∃ (s : Finset V) (f : V → K), (↑s ⊆ S) ∧ (∀ v ∉ s, f v = 0) ∧ (x = Finset.sum s (fun v => f v • v))
/-- Any vector in $S$ is trivially a linear combination of $S$. -/
theorem linear_combination_of_mem {S : Set V} {v : V} [DecidableEq V] (hv : v ∈ S) : is_linear_combination K V S v := by


  use {v}, (λ w => if w = v then (1 : K) else 0)
  -- We choose the finite set `{v}` and define coefficients f such that f(v) = 1 and f = 0 on other vectors.
  simp only [Finset.coe_singleton, Finset.singleton_subset_iff]
  constructor
  exact Set.singleton_subset_iff.mpr hv
  -- All elements of `{v}` (just v itself) are in S by assumption.
  simp  -- Outside `{v}`, f is 0 by construction.
  symm
  exact VectorSpace.one_smul v
