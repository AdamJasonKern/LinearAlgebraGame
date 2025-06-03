import Game.Metadata
import Mathlib.Algebra.Module.Basic  -- import basic algebraic structures
import Mathlib.Data.Set.Basic

World "VectorSpaceWorld"
Level 1

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

-- Level 1: VectorSpace.lean


-- A vector space over field K with additive group V
class VectorSpace (K V : Type) [Field K] [AddCommGroup V] extends SMul K V where
  smul_add : ∀ (a : K) (x y : V), a • (x + y) = a • x + a • y           -- distributivity of scalar over vector addition
  add_smul : ∀ (a b : K) (x : V), (a + b) • x = a • x + b • x           -- distributivity of scalar addition
  mul_smul : ∀ (a b : K) (x : V), (a * b) • x = a • (b • x)             -- compatibility of scalar multiplication
  one_smul : ∀ (x : V), (1 : K) • x = x                                -- identity scalar acts as identity

-- (No proof required in this level; the definition sets up the axioms for later use.)
-- Level 2: Subspace.lean
--import Game.Levels.LinearAlgebra.L01_VectorSpace


variable (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V]

/-- `isSubspace K V W` means W is a subspace of V (nonempty and closed under addition and scalar multiplication). -/
def isSubspace (W : Set V) : Prop :=
  W.Nonempty ∧ (∀ (x y : V), x ∈ W → y ∈ W → x + y ∈ W) ∧ (∀ (a : K) (x : V), x ∈ W → a • x ∈ W)

-- (No proof required; this is a definition. In subsequent levels, you'll prove properties of subspaces.)
-- Level 3: AdditiveIdentity.lean
--import Game.Levels.LinearAlgebra.L02_Subspace

variable (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V]

/-- If W is a subspace of V, then the zero vector (additive identity) of V is in W. -/
Statement subspace_contains_zero {W : Set V} (hW : isSubspace K V W) : (0 : V) ∈ W := by
  /- Hint: Use the fact that W is nonempty. Pick an element w ∈ W (from hW.1),
     then use closure under scalar multiplication with scalar 0.
     Remember that (0 : K) • w = 0 (the zero vector) by a consequence of the vector space axioms. -/
  obtain ⟨w, hw⟩ := hW.1                     -- W.Nonempty gives an element w in W
  have calc_zero : (0 : K) • w = ((0 : K) + (0 : K)) • w := by
    rw [zero_add]
  -- Using the distributivity axiom: 0 • w + 0 • w = (0 + 0) • w = 0 • w
  symm at calc_zero
  rw [VectorSpace.add_smul (0 : K) (0 : K) w] at calc_zero    -- now calc_zero: 0 • w = 0 • w + 0 • w
  -- Subtract 0 • w from both sides (using additive cancellation) to obtain 0 = 0 • w
  have hg :  (0:V)+(0 : K) • w =(0 : K) • w := by exact AddRightCancelMonoid.zero_add (0 • w)
  nth_rw 3 [hg.symm] at calc_zero
  have : (0 : V) = (0 : K) • w := by
    symm
    exact add_right_cancel  calc_zero       -- cancel 0•w from the equation
  rw [this]
  -- Now 0 = 0 • w shows (0 : V) is obtained by scalar-multiplying w, hence 0 ∈ W
  exact hW.2.2 0 w hw         -- by closure under scalar multiplication, 0 • w ∈ W

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
