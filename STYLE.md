# Style Guide

## Coding style conventions
We are not aware of any official Agda "style guide" or similar; please let us know if you know of one.  Otherwise, please try to be consistent with style used in the repo so far and/or contribute here by helping to establish more detailed guidance.

Please ensure that there are no trailing spaces before creating a pull request; [this script](./Scripts/remove-trailing-whitespace.sh) is useful for this purpose.

## Assumptions, warnings and overrides
We aim for a clean proof with all assumptions well justified and minimal warnings and overrides thereof.  Where practical, we will adhere to the following guidelines (and ask contributors to do so as well).

To help keep track of valid assumptions and overrides (as opposed to those made temporarily to support progress in other areas), we aim to annotate any outstanding issues to indicate whether they are temporary (and thus a [`TODO-n`](./TODO.md) can be created for addressing them), or are considered valid and are not a threat
to validity of proofs (with explanation),
or if there is some technical issue preventing us from addressing them.

Here we list some relevant types of issues and discuss how they should be annotated:

 - `postulate`s
	 - For valid assumptions, include comment `valid assumption` on the same line as the `postulate` keyword (enabling easy exclusion from searches for issues that remain to be resolved, as well as easy searching for assumptions on which our proof depends).
	 - For properties that are `postulate`d simply because nobody has proved them yet, include comment `TODO-n: prove` (where `n` is chosen following [these guidelines](./TODO.md)).
	 - For any others, include comment `temporary`, along with an explanation of the reason for the `postulate` and a summary of issues relevant to eliminating it.
 - Pragmas to override warnings/errors should be commented and explained, similar to "other" `postulate`s above.  Examples include:
   - `{-# TERMINATING #-}`
   - `{-# OPTIONS --allow-unsolved-metas #-}`
 - Similarly, warnings (represented by different font faces) should be eliminated where possible, and if any remain, they should be explained and justified.  Examples include:
   - Unsolved metas
   - Catchall clauses
   - Unreachable clauses