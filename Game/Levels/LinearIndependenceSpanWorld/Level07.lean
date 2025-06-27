/-by_cases

funext

Finset.coe_union

Set.union_subset

sub_smul

Finset.sum_sub_distrib

Finset.subset_union_left

Finset.subset_union_right

Finset.sum_subset

sub_eq_zero

Finset.not_mem_union-/
import Game.Levels.LinearIndependenceSpanWorld.Level05

World "LinearIndependenceSpanWorld"
Level 7

Introduction "This is the \"boss level\" of the Linear Independence and Span World. This level is a
proof that in a linearly independent set, linear combinations are unique. There are also a few new tactics
and multiple new theorems you should use.

### The Goal
In this level, we have 5 objects and 6 hypotheses about those objects. We have the set `S : Set V`,
which is the linearly independent set we are working with. We also have `s` and `f`, which are the set
and function we are summing over to get the first linear combination, and `t` and `g` are the second
linear combination. We have `hs : linear_independent_v K V S`, which states that `S` is linearly independent,
`hs : ↑s ⊆ S` and `ht : ↑t ⊆ S`, which state that `s` and `t` are both in `S`, so are valid linear
combinations of `S`. We know `hf0 : ∀ v ∉ s, f v = 0` and a similar `hg0`, which state that both functions
are zero outside of their domain. This helps us prove `f = g`, since otherwise we wouldn't know what
the values of `f` and `g` would be outside of `s` and `t`. Lastly, we have `heq : Finset.sum s (fun v => f v • v) = Finset.sum t (fun v => g v • v)`,
which shows that the two linear combinations are equal. We then must pove that `f = g`

### The `specialize` tactic
The `specialize` tactic can be thought of as the opposite of `use`. While `use` helps specify a value
for a `∃` in the goal, `specialize` specifies a value for a `∀` in a hypothesis. For example, if you
have a hypothesis `h : ∀ v : V, v • 1 = v`, and you have a vector `x : V`, then `specialize h x` will
change `h` to `h : x • 1 = x`. `specialize` also works if `h` is an implication. If `h1 : P → Q` is a
hypothesis, and `h2 : P` is a proof of `P`, then `specialize h1 h2` will change `h2` to `h2 : Q`.

### The `by_cases` tactic
The `by_cases` tactic helps you prove something by cases. If you want to prove a statement about vectors
in `V`, but you want to split into cases where `v = 0` or `v ≠ 0`, `by_cases hv : v = 0` will split the
goal into two subgoals: one where you have a hypothesis `hv : v = 0`, and another where you have a hpyothesis
`hv : v ≠ 0`.

### The `funext` tactic
The `funext` tactic lets you prove statements about functions. It works similarly to the `intro` tactic,
where you introduce an arbitrary object, but instead of introducing from a `∀` statment, it works if
you have a goal of the form `f = g`, where `funext x` will chang ethe goal to the form `f x = g x`, and
give you an arbitrary `x` in the domain of `f` and `g`.

### New theorems
This level requires multiple new theorems, particularly ones about Finsets and sums. There are two theorems
about vector spaces that can be proven quite easily, but they are still nice to have without needing
to prove them first. Instead of explaining them all here, you can look at them on the right side of
the screen. The new theorems are: `Finset.coe_union`, `Set.union_subset`, `sub_smul`, 'Finset.sum_sub_distrib',
`Finset.subset_union_left`, `Finset.subset_union_right`, `Finset.sum_subset`, `sub_eq_zero`, and `Finset.not_mem_union`.
If you need more theorems, you can either prove them in lemmas, or if you want, you can go to the world
select menu and turn \"Rules\" to \"none\", which should allow you to use any tactic or theorem in Lean.

### Proof overview
If you look at the hypotheses you have, the most important ones are that S is linearly independent and
that the two sums are equal. When you have a statement that a set is linearly independent, it is often
very helpful to try to find the correct set and function to sum over, then try to satisfy the assumptions
to prove that the function must be zero. Since the goal is to prove that `f = g`, maybe try to prove
instead that `f - g = 0`, so you can try proving the assumptions in `hS` with the function `f - g`. You
also need to pick the correct set to be summing over. Since this set must contain both `s` and `t`, you
can use `s ∪ t`. Also, note that this will then only prove that `f = g` on the set `s ∪ t`, so you may
need to use `by_cases` to prove it outside `s ∪ t`.
"

open VectorSpace
variable (K V : Type) [Field K] [AddCommGroup V] [DecidableEq V] [VectorSpace K V]

Statement linear_combination_unique
{S : Set V} (hS : linear_independent_v K V S)
(s t : Finset V) (hs : ↑s ⊆ S) (ht : ↑t ⊆ S)
(f g : V → K) (hf0 : ∀ v ∉ s, f v = 0) (hg0 : ∀ v ∉ t, g v = 0)
(heq : Finset.sum s (fun v => f v • v) = Finset.sum t (fun v => g v • v)) :
f = g := by
  Hint "First, note that you have a goal of proving two functions equal. Try to instead prove it for
  an arbitrary value."
  funext v

  Hint "Now, we can split into cases where either v ∈ (s ∪ t) or not."
  by_cases h : v ∈ (s ∪ t)
  unfold linear_independent_v at hS

  Hint "Think about the forwards proof. What set and function are we summing over when applying the linear independence of S?"
  specialize hS (s ∪ t) (f - g)

  Hint "We now want to show `↑(s ∪ t) ⊆ S`. This is a type casted union. Instead, we want a union of
  type casts, so that we can use theorems having to do with unions. One of the theorems should help with this"
  rw[Finset.coe_union] at hS

  specialize hS (Set.union_subset hs ht)

  Hint "Now, we have to show that `(Finset.sum (s ∪ t) fun v => (f - g) v • v) = 0`. This will
  be difficult, so try proving it with a `have` statement"
  have lemmaSumDiffEqZero : (Finset.sum (s ∪ t) fun v => (f - g) v • v) = 0 := by
    Hint "It would be nice if we could distribute the `f - g` through the `•` operator. Try proving
    `(fun v => (f - g) v • v) = (fun (v : V) => ((f v) • v) - ((g v) • v))` with another `have` statement"
    have fun_dist : (fun v => (f - g) v • v) = (fun (v : V) => ((f v) • v) - ((g v) • v)) := by
      funext v
      exact sub_smul (f v) (g v) v

    rw[fun_dist]

    Hint "Now, we can split the sum in two"
    rw[Finset.sum_sub_distrib]

    Hint "We now have two sums. The first one should be equivalent to our first linear combination,
    and the second should be equivalent to our second linear combination. We need to change the sets
    they are being summed over. We have a theorem that can do this, but it needs a hypothesis that we
    don't have. Try proving these hypotheses with a `have` statement."
    have hfprod0 : ∀ v ∈ s ∪ t,  v ∉ s → f v • v = 0 := by
      intros v _hv1 hv2
      rw[hf0 v hv2]
      exact zero_smul K v

    have hgprod0 : ∀ v ∈ s ∪ t,  v ∉ t → g v • v = 0 := by
      intros v _hv1 hv2
      rw[hg0 v hv2]
      exact zero_smul K v

    rw [(Finset.sum_subset (f := fun v => f v • v) (Finset.subset_union_left s t) hfprod0).symm]
    rw [(Finset.sum_subset (f := fun v => g v • v) (Finset.subset_union_right s t) hgprod0).symm]

    Hint "Now, we use the fact that the two sums are equal to finish the proof of the lemma"
    rw[heq]
    simp

  Hint "Now, we simply have to prove the requirements of hS"
  specialize hS lemmaSumDiffEqZero

  specialize hS v h

  Hint "We know now from hS that f v - g v = 0, and one of the new theorems lets us finish the proof.
  Remember that if you have a proof of `↔`, `.1` will be a proof of the forwards direction and `.2` the
  backwards."
  exact sub_eq_zero.1 hS

  rw[Finset.not_mem_union] at h
  cases' h with hS hT

  rw[hf0 v hS, hg0 v hT]
