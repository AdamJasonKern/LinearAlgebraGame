import Game.Metadata

World "TutorialWorld"
Level 4
Title "Level Four"

Introduction "
# Tutorial World
## Level 4: The `split`, `cases` tactics

In this level we will learn `split` and `cases` in the context of logical 'and' (∧) and 'or' (∨).

## split:

The logical symbol `∧` means 'and'. If $P$ and $Q$ are propositions, then
$P land Q$ is the proposition '$P$ and $Q$'. If your *goal* is `P ∧ Q` then
you can make progress with the `split` tactic, which turns one goal `⊢ P ∧ Q`
into two goals, namely `⊢ P` and `⊢ Q`. In the level below, after a `split`,
you will be able to finish off the goals with the `exact` or `apply` tactic.
"

/- Lemma : no-side-bar
If $P$ and $Q$ are true, then $P\land Q$ is true.
-/
Statement (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  exact p
  exact q



Conclusion "
The message shown when the level is completed
"
