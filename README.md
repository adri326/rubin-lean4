# Lean4 port of the proof of Rubin's Theorem

THis repository contains a (WIP) computer proof of Rubin's Theorem,
which states that if a group acts on two topological spaces while satisfying enough conditions,
then there exists a homeomorphism between those two topological spaces,
such that the homeomorphism preserves the group structure of the group action.

It is based on ["A short proof of Rubin's Theorem"](https://arxiv.org/abs/2203.05930) (James Belk, Luke Elliott and Franceso Matucci),
and a good part of the computer proof was written in Lean 3 by [Laurent Bartholdi](https://www.math.uni-sb.de/ag/bartholdi/).

The eventual goal of this computer proof is to have it land into [Mathlib](https://github.com/leanprover-community/mathlib4).

## Installation and running

You will need an installation of [`elan`](https://github.com/leanprover/elan) and `git`.

Then, simply run the following:

```sh
# Clone this repository
git clone https://github.com/adri326/rubin-lean4

# Navigate to the folder created by git
cd rubin-lean4

# This will download mathlib, and try to download a set of pre-compiled .olean files,
# so you won't have to re-compile the entirety of mathlib again (which takes a good hour or two)
lake exe cache get

# Build the code (if no errors are printed then Lean was happy)
lake build
```
