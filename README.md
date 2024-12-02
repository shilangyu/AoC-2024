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
