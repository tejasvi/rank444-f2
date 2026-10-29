import Lean

/-! # `#assert_std_axioms c`: fail unless `c` depends only on propext, Classical.choice and Quot.sound

A compile-time axiom gate for the E1x modules (the axioms of the release are exactly these three). Unlike
`#print axioms`, it turns a non-standard axiom (e.g. `sorryAx`, `Lean.ofReduceBool`) into a compile error, so a
successful compile is the census. The axiom list is logged as information. -/

open Lean Elab Command

elab "#assert_std_axioms " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let axs ← liftCoreM (collectAxioms n)
  let bad := axs.filter (fun a => !(a == ``propext || a == ``Classical.choice || a == ``Quot.sound))
  unless bad.isEmpty do
    throwError "axiom gate: {n} depends on non-standard axioms {bad} (all: {axs})"
  logInfo m!"axiom gate: {n} depends on {axs}"
