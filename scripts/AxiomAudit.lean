/-
Axiom audit for the `ProofOfSpace` development.

Run from the `lean/` directory:

    lake env lean scripts/AxiomAudit.lean

Exit code `0` means every declaration in the `ProofOfSpace` namespace depends only on
the three axioms classical Lean itself is built on -- `propext`, `Classical.choice` and
`Quot.sound` -- and in particular that none of them depends on `sorryAx`.  This is the
claim `README.md` makes under "How to Execute", checked mechanically rather than by
reading `#print axioms` output by hand.

The file is deliberately outside the `ProofOfSpace` library root, so `lake build` does
not compile it; it is a checker, not part of the development.
-/
import ProofOfSpace
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

namespace AxiomAudit

/-- The axioms of classical Lean that the development is allowed to rest on. -/
def allowed : NameSet :=
  NameSet.empty
    |>.insert ``propext
    |>.insert ``Classical.choice
    |>.insert ``Quot.sound

end AxiomAudit

run_cmd do
  let env ← getEnv
  let names : Array Name :=
    env.constants.fold (init := #[]) fun acc n _ =>
      if (`ProofOfSpace).isPrefixOf n && !n.isInternal then acc.push n else acc
  let mut offenders : Array (Name × Array Name) := #[]
  for n in names do
    let axs ← collectAxioms n
    let bad := axs.filter fun a => !AxiomAudit.allowed.contains a
    unless bad.isEmpty do
      offenders := offenders.push (n, bad)
  if offenders.isEmpty then
    logInfo m!"axiom audit passed: {names.size} declarations in `ProofOfSpace` \
      depend only on propext, Classical.choice and Quot.sound"
  else
    let report := offenders.map fun (n, bad) => m!"{n} depends on {bad.toList}"
    throwError "axiom audit failed:{indentD (MessageData.joinSep report.toList "\n")}"
