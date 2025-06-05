import Game.Metadata

World "TutorialWorld"
Level 10

Title "The simp tactic"

Introduction "`simp` is a tactic which tries to prove equalities using facts in its database.
Ideally, the database of facts would result in expressions
being simplified into a normal form. In practice, this is often unachievable
(normal forms may not exist, or there may not exist a collection of rewrite rules that produce them),
but nevertheless we aim to approximate this ideal where possible. Even better, we would like the database
of facts to be confluent, meaning the order in which the simplifier considers rewrites does not matter. Again, we aim to be close to confluent where possible.

While this system is able to prove many simple statements completely automatically, proving all simple statements is not part of its job description, as disappointing as that might be.

Here is an example (using mathlib).


## Details

The `simp` tactic does basic automation. `Simp` is able
to solve all equalities whose proofs involve a tedious number
of rewrites of other tactics which have already been introduced.

The following lemma is an example. (If you haven't seen the following definition, don't worry! The lemma we're proving is simple!)

We defined an algebraic structure (a set G equipped by a binary operation denoted by *) called a \"group\" by the following axioms:

Associativity: for elements a, b, and c in the group G, $a * (b * c) = (a * b) * c$.
Identity: there's the identity element 1 such that $1 * g = g * 1 = g$ for all elements g in G.
Inverse: for each element g in G, there exists an inverse for it, $g⁻¹$, such that they \"annihilate\": $g⁻¹ * g = g * g⁻¹ = 1$.
-/

/-
As we've already defined such axoims and properties, including:
[mul_right_inv]: a * a⁻¹ ==> 1
[mul_one]: 1 * 1 ==> 1
[one_mul]: 1 * b ==> b
[mul_inv_cancel_right]: b * c * c⁻¹ ==> b
[eq_self_iff_true]: b = b ==> true

Solely using `simp` will close the goal.
"

Statement (G : Type) [Group G] (a b c : G)  : a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  simp

Conclusion "This last message appears if the level is solved."
