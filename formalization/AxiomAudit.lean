import LowLogitRank

/-! Axiom audit.

For every declaration defined in a module of the `LowLogitRank` library (whatever its
namespace, private declarations included) this file collects the axioms it depends
on and fails unless they are among `propext`, `Classical.choice` and `Quot.sound`. It also lists
every theorem whose docstring cites a statement of the paper by TeX label (`lem:...`, `thm:...`,
`prop:...`, `cor:...`, `eq:...`, `sec:...`), one line per theorem, as `AUDIT <name> <labels>`. -/

open Lean Elab Command

/-- The TeX labels cited in a docstring, in backquotes. -/
def citedLabels (doc : String) : List String :=
  let prefixes := ["lem:", "thm:", "prop:", "cor:", "eq:", "sec:", "alg:"]
  (doc.splitOn "`").filter fun piece =>
    prefixes.any (fun p => piece.startsWith p) && !piece.contains ' '

#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut lines : Array String := #[]
  let ours : Name → Bool := fun n =>
    match env.getModuleIdxFor? n with
    | some idx => (`LowLogitRank).isPrefixOf (env.header.moduleNames[idx.toNat]!)
    | none => false
  for (n, ci) in env.constants.toList do
    if ours n then
      checked := checked + 1
      let axs ← Lean.collectAxioms n
      let extra := axs.filter (fun a => !allowed.contains a)
      if !extra.isEmpty then bad := bad.push (n, extra)
      if ci matches .thmInfo _ && !n.isInternal then
        if let some doc ← liftIO (findDocString? env n) then
          let labels := citedLabels doc
          if !labels.isEmpty then
            lines := lines.push s!"AUDIT {n} {String.intercalate "," labels.eraseDups}"
  let sorted := lines.qsort (· < ·)
  logInfo (String.intercalate "\n" sorted.toList)
  logInfo m!"GLOBAL {checked} declarations checked, {bad.size} with nonstandard axioms"
  unless bad.isEmpty do
    throwError m!"nonstandard axioms: {bad}"
