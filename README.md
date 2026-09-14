# Proofs of space: two Lean projects

This repository contains two independent Lean projects for separate Palomar entries.
Each has a small self-contained `Challenge.lean`, a matching `Solution.lean`, a
pinned Lake environment, metadata, and selected Comparator declarations.

| Project directory | Registered theorem | Comparator configuration |
| --- | --- | --- |
| [drsample](drsample/README.md) | DRSample, BucketSample, and HarmonicSample | `drsample/comparator.json` |
| [pebbling_latency](pebbling_latency/README.md) | `ProofOfSpaceStatement.pebbling_latency` | `pebbling_latency/comparator.json` |

The sampler results use deletion constant `1/18000`, block-width constant
`3600`, and failure coefficient `1/11000` for every `n ≥ 2^120`. The depth
constant is `1.48` for DRSample and BucketSample and `2` for HarmonicSample;
both samplers with multiple draws cover every integer `r ≥ 1`. The latency
project retains its probability and conditional 18-layer Filecoin
specializations as supporting results.

Both Challenges import Mathlib alone. The sampler Challenge has three
intentional theorem placeholders, and the latency Challenge has one.
Proofs and auxiliary results belong to the supporting modules and
`Solution.lean`.

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
