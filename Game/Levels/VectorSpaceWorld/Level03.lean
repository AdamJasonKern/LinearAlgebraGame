import Game.Levels.VectorSpaceWorld.Level02

namespace LinearAlgebraGame

World "VectorSpaceWorld"
Level 3

Title "Scaling by -1"

/--
This is a proof that `-1 • v = -v`, that multiplying by the -1 scalar gives the inverse vector.
-/
TheoremDoc LinearAlgebraGame.neg_one_smul_v as "neg_one_smul_v" in "Vector Spaces"

Introduction "We now understand scaling by `0` very well. We also have an axiom that scaling by `1`
acts as the identity. The next step is to see what scaling by `-1` does. Intuitively, it should
cancel out the vector scaled by `1`, so it should be the additive inverse of the vector.

The goal of the level is to prove this.

A few hints that could help:
The defining property of `-v` is that `-v + v = 0`. The `simp` tactic can use this. Try to use this
in your proof.
You can also use the theorems proven in previous levels.

### Difficulty with `one_smul`
You may eventually try to rewrite a vector `v` as `1 • v` in this level. However, trying
`rw[(one_smul v).symm]` may run into errors. This is because `one_smul v` only takes an element of `V`
as input, so Lean doesn't know which field \"K\" to use to get the \"1\" from. To fix this, try
`one_smul K v` to tell Lean which \"K\" you are using.

### `neg_add_self` theorem
In order to work with negatives, we also have the theorem `neg_add_self`. This is a proof that `-x + x = 0`.
Similarly to `zero_add`, this theorem works in both K and V. This allows you to cancel out negatives.
"

/--
`neg_add_self` is a proof that "-x + x = 0. This holds whether x is in K or V.
-/
TheoremDoc neg_add_self as "neg_add_self" in "Groups"

/--
`neg_add_self` is a proof that "-x + x = 0. This holds whether x is in K or V.
-/
TheoremDoc add_neg_self as "add_neg_self" in "Groups"

NewTheorem neg_add_self add_neg_self

DisabledTactic simp linarith

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

/--
In any vector space V over K, multiplying a vector by -1 gives its additive inverse.
-/
Statement neg_one_smul_v (v : V) : (-1 : K) • v = -v := by
  Hint "A good first step is cancelling out the `-v` term on the right."
  Hint (hidden := true) "Try `apply add_right_cancel (b := v)`"
  apply add_right_cancel (b := v)
  Hint "Remember the `nth_rw m [theorem]` tactic to only rewrite the mth instance."
  Hint (hidden := true) "Try `nth_rw 2 [(one_smul K v).symm]`"
  nth_rw 2 [(one_smul K v).symm]
  Hint (hidden := true) "Try `rw[(add_smul (-1 : K) (1 : K) v).symm]`"
  rw [(add_smul (-1 : K) (1 : K) v).symm]
  Hint (hidden := true) "Try `rw[neg_add_self]`"
  rw[neg_add_self]
  Hint (hidden := true) "Try `rw[neg_add_self]`"
  rw[neg_add_self]
  Hint "This looks like something we've done before. Either the `rw` or `exact` tactics should solve the goal"
  Hint (hidden := true) "Try `exact zero_smul_v K V v`"
  exact zero_smul_v K V v

Conclusion "We now have many theorems relating to vector spaces! In the next levels, we will introduce
the idea of a \"subspace\"."
