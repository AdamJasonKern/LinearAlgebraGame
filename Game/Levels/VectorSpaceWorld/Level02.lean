/-import Game.Metadata
import Game.Levels.VectorSpaceWorld.Level01

World "VectorSpaceWorld"
Level 2

Title "Hello World"

Introduction ""


variable (K V : Type) [Field K] [AddCommGroup V] [VectorSpace K V]
theorem zero_smul_v (w : V) : (0 : K) • w = (0:V):= by
  have calc_zero : (0 : K) • w = ((0 : K) + (0 : K)) • w := by
    rw [zero_add]
  rw [VectorSpace.add_smul (0 : K) (0 : K) w] at calc_zero
  have hg : (0 : K) • w = (0:V)+(0 : K) • w := by exact Eq.symm (AddRightCancelMonoid.zero_add (0 • w))
  nth_rw 1 [hg] at calc_zero
  apply add_right_cancel at calc_zero
  exact symm calc_zero

/-- In any vector space V over K, multiplying a vector by -1 gives its additive inverse. -/
theorem neg_one_smul_v (v : V) : (-1 : K) • v = -v := by
  /- Hint: Use the fact that (-1 + 1) = 0. Apply the `add_smul` axiom:
     $(-1 + 1) • v = (-1)•v + 1•v$.
     Simplify the left side to 0 • v (which is 0 by Level 6),
     and simplify 1 • v to v.
     Then solve the equation 0 = (-1)•v + v$ for $(-1)•v$. -/
  have step1 : (0 : K) • v = ((1 : K) + (-1 : K)) • v := by rw [add_right_neg]
  rw [VectorSpace.add_smul] at step1                    -- now step1: 0 • v = (-1)•v + 1•v
  rw [zero_smul_v K V v, VectorSpace.one_smul] at step1   -- substitute 0•v = 0 and 1•v = v
  -- Now we have 0 = (-1)•v + v, which means (-1)•v is the additive inverse of v
  symm at step1
  symm
  exact neg_eq_of_add_eq_zero_right step1  -- so (-1)•v = -v

--
#check zero_smul
Statement subspace_neg {W : Set V} [Field K] [AddCommGroup V] [VectorSpace K V] (hW : isSubspace K V W) : ∀ (x : V), x ∈ W → (-x) ∈ W := by
  /- Hint: Use closure under scalar multiplication with the scalar -1.
     If x ∈ W, then (-1) • x ∈ W by hW. Also, from the vector space axioms, (-1) • x = -x. -/
  intros x hx
  have h_neg : (-1 : K) • x ∈ W := hW.2.2 (-1) x hx    -- closure: -1 • x is in W
  -- To show (-1)•x = -x, use that (-1 + 1) • x = (-1)•x + 1•x and simplify:
  have eq_inv := calc
    (0 : K) • x = ((1:K) + (-1: K)  ) • x                 := by rw [add_right_neg]   -- (-1 + 1 = 0)
              _ = (1:K) • x + (-1: K) • x  := by rw [VectorSpace.add_smul]
  -- Simplify the right-hand side using 1 • x = x and 0 • x = 0:
  rw [VectorSpace.one_smul] at eq_inv            -- now eq_inv: 0 • x = (-1)•x + x
  rw [zero_smul_v] at eq_inv                       -- 0 = (-1)•x + x   (0•x is 0 by Level 6 result or proven similarly)
  -- The equation 0 = (-1)•x + x means (-1)•x is the additive inverse of x, i.e. (-1)•x = -x
  have : (-1 : K) • x = -x :=by exact neg_one_smul_v K V x
  symm at this
  rwa [←this] at h_neg   -- replace (-1)•x with -x in the membership proof
-- Level 5: SubspaceAxioms.lean

Conclusion ""
-/
