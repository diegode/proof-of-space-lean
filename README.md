# Proofs of space: two Lean projects

This repository contains two independent Lean projects for separate Palomar entries.
Each has a small self-contained `Challenge.lean`, a matching `Solution.lean`, a
pinned Lake environment, metadata, and one selected Comparator declaration.

| Project directory | Registered theorem | Comparator configuration |
| --- | --- | --- |
| [drsample](drsample/README.md) | `ProofOfSpaceStatement.drsample_conjecture2` | `drsample/comparator.json` |
| [pebbling_latency](pebbling_latency/README.md) | `ProofOfSpaceStatement.pebbling_latency` | `pebbling_latency/comparator.json` |

The DRSample result uses `(c₁,c₂,c₃) = (1/20000,1,3072)` and retains the stronger
finite depth estimates and the ideal indegree-six Filecoin corollary in its
proof library. The latency project retains its probability and conditional
18-layer Filecoin specializations as supporting results.

Both Challenges import Mathlib alone. They contain only the definitions needed
to state their main theorem and one intentional `sorry`. Proofs and auxiliary
results belong to the supporting modules and `Solution.lean`.

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
