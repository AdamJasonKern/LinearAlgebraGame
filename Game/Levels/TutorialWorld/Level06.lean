import Game.Metadata

World "TutorialWorld"
Level 6
Title "Level Eight"

Introduction "
Axiom : not_iff_imp_false (P : Prop) :
¬ P ↔ P → false
-/

lemma not_iff_imp_false (P : Prop) : ¬ P ↔ P → false := iff.rfl -- hide

/-
# Tutorial World

## Level 8 : More on Proof By Contradiction

## `exfalso`
-/


/-


It's certainly true that $P land( lnot P) implies Q$ for any propositions $P$
and $Q$, because the left hand side of the implication is false. But how do
we prove that `false` implies any proposition $Q$?

A cheap way of doing it in
Lean is using the `exfalso` tactic, which changes any goal at all to `false`.
You might think this is a step backwards, but if you have a hypothesis `h : ¬ P`
then after `rw not_iff_imp_false at h,` you can `apply h,` to make progress.
"

/- Lemma : no-side-bar
If $P$ and $Q$ are true/false statements, then
$$(P\land(\lnot P))\implies Q.$$
-/
Statement (P Q : Prop) : (P ∧ ¬ P) → Q := by
  intro h
  cases h with
  | intro p np =>
  exfalso
  apply np
  exact p

Conclusion "
The message shown when the level is completed
"
