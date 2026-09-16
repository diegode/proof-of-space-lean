# Proofs of space: two Lean projects

This repository contains two independent Lean projects for separate Palomar entries.
Each has a small self-contained `Challenge.lean`, a matching `Solution.lean`, a
pinned Lake environment, metadata, and selected Comparator declarations.

| Project directory | Registered theorem | Comparator configuration |
| --- | --- | --- |
| [drsample](drsample/README.md) | Ten results (eleven declarations); see project inventory | `drsample/comparator.json` |
| [pebbling_latency](pebbling_latency/README.md) | `ProofOfSpaceStatement.pebbling_latency` | `pebbling_latency/comparator.json` |

The sampler project now states exponent-dependent bounds: for each fixed
`0 < ε < 1`, the deletion budget is `Θ(ε n/L(n))`, depth is
`Ω(n/(log₂ n)^ε)`, and block width is `Θ(L(n)/ε)`. The block-to-fractional
conversion also gives both samplers two-sided fractional robustness for any
fixed fraction below one half. All ten required paper results have proofs and
matching Challenge statements, including Valiant depth reduction, balanced
optimality, and the general conditional-label multiscale theorem. The
[sampler inventory](drsample/README.md#complete-paper-inventory) excludes the
cited BRG pebbling corollary, as requested. The latency project proves
reference-trajectory amplification with explicit repair accounting.

Both Challenges import Mathlib alone. Their intentional theorem placeholders
have proofs in supporting modules and `Solution.lean`.

Build and verify from the repository root:

```sh
lake -d drsample build
lake -d pebbling_latency build
./scripts/verify-comparator.sh
```

The verifier script can also select one project by name. It shares its pinned
tool cache between the projects; each project has its own Lake build state.
The repository-root Apache-2.0 license covers both.

For Palomar, select the project directory and repository-relative Comparator
path from the table, and the corresponding `formalization.yaml` inside that
project. The two configurations describe two separate entries. These source
files prepare the entries; they do not submit or publish them.

See [Palomar's submission rules](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
for nested projects and the approved Challenge import closure.
