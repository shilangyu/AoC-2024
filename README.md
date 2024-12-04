# AoC-2024

Advent of Code 2024 where each day contains a formal proof about something related to the task.

Occasionally may also contain actual solutions.

## Day 1

Using the fact that subtraction on natural numbers is saturated in Lean, we prove that the standard absolute function implementation

```lean
if x > y then x - y else y - x
```

is equivalent to

```lean
(x - y) + (y - x)
```

Then we note that a counting function over a list is the same as taking the length of a filtered list.

```lean
l.count x = (l.filter (Eq x)).length
```

## Day 2

If a list `[a, ...b]` is safe then so is `[...b]`. This lemma allows to derive a bound on the last element of a safe list:

Given a non-empty safe list $l$, let $s$ be the first element of it and $e$ be the last one. Then it always holds that:

$$
	e \le s + 3 \cdot len(l) \quad\land\quad e \ge s - 3 \cdot len(l)
$$

## Day 3

We define what it means to be a regular expression and by construction prove that the `mul()` language is a regular one. This means the pattern can be extracted using regex engines.

## Day 4

We prove that looking for a sequence of characters in a string is equivalent to looking for the reverse sequence of characters in a reversed string.

Notably from this theorem and a lemma showing that reversing a string is an involution, a corollary follows that looking for XMAS in the reverse of a string is the same as looking for SAMX in a string.
