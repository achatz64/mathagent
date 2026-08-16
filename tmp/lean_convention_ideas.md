# Tactic mode


## Readability suggestions

1. Don't use `\.` for `constructor` cases if the proofs are long, use `case name => ...` instead.

2. If more than one _? are to be handled, they have to be named and `case` must be used or if the statements are short and well-readable `show` can be used. So: show when the goal is short, named holes when it isn't.  

3. Use named attributes where possible, for example for `h : t <-> s` use `h.mpr` instead of `h.2`. 