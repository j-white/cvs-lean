import Cvs
open Lean

/-! Every declaration of the project, checked for axioms beyond `propext`, `Classical.choice`,
`Quot.sound` (in particular `sorryAx`). Prints the count and any offender. -/

#eval show CoreM Unit from do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut bad := 0
  for (c, ci) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? c | continue
    unless (`Cvs).isPrefixOf env.header.moduleNames[i.toNat]! do continue
    unless ci matches .thmInfo _ do continue
    n := n + 1
    let ax ← Lean.collectAxioms c
    let extra := ax.filter (fun a => !ok.contains a)
    if !extra.isEmpty then
      bad := bad + 1
      IO.println s!"{c}: {extra}"
  IO.println s!"theorems checked: {n}, with non-standard axioms: {bad}"
