import Game.Metadata

World "TutorialWorld"
Level 6
Title "Level Six"

Introduction "
# Tutorial World

## Level 6: The `linarith` tactics

Similar to the `ring` tactic, linarith (linear arithmatic）also aims to simplify the process of proofs.
Specifically, it solves certain kinds of linear equalities and inequalities.
Unlike the ring tactic, linarith uses hypotheses in the tactic state.

If you have a bunch of hypotheses like h1 : a < b, h2 : b <= c, h3 : c = d and a goal of a < d,
then linarith will solve it. Linarith knows how to combine linear relations: it knows a ton of results about how to put inequalities together and will close such goals.

"

/- Lemma : no-side-bar
If $x y a b$ are natural numbers, and if $x < y$, $a < b$, then $ x + a <  y + b$.



linarith
-/
Statement linarith (x y a b : Nat) (h1 : x < y) (h2: a < b) : x + a < y + b := by
  sorry

Conclusion "
YAY!!!!
"
