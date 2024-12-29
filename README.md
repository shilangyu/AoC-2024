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

## Day 5

We prove the correctness of an algorithm to check if some update is ordered. Given all the `X|Y` "X comes before Y" instructions we can construct a linear order. Linear orders over finite sets are serializable into a list which identify that order. Once such a list is constructed, checking whether an update is correct is just a matter of checking that the update is a non-continuous sublist of the linear order list.

Example:

```
47|53
97|13
97|61
97|47
75|29
61|13
75|53
29|13
97|29
53|29
61|53
97|53
61|29
47|13
75|47
97|75
47|61
75|61
47|29
75|13
53|13
```

There are $\frac{n(n-1)}{2}$ consistent comparisons (where $n$ is the amount of numbers) so it forms a linear order. Since $n$ is finite, we can serialize these comparisons into a list: [97, 75, 47, 61, 53, 29, 13].

Now to check if the update [75, 47, 53, 29] is correct, it is enough to check that it is a non-continuous sublist: [97, **75**, **47**, 61, **53**, **29**, 13].

This is an $O(n)$ algorithm compared to the naive $O(n^2)$ one.

## Day 6

We implement the move simulation function in a type-safe way (all indices are type-guaranteed to be in range). We then show that there exists a map for which moving never stops, namely the following map:

```
.#.
#^#
.#.
```

This is proven by showing that all modulo 4 moves have the same configurations.
