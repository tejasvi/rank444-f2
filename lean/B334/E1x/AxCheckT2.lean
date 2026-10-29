import Lean

/-! # `#assert_axioms_T2 c`: the axiom gate for runs whose leaves use T2's native-chunk records

The runs of classes 613, 615, 618, 619, 663, 665, 667 and 682 cover some of their leaves by records of the native
chunks `T2.nl_<c>`, whose `leafS` facts come from `B334.T2.nat_ok`, proved by `native_decide` (the approved option-B
trust base). Their theorems therefore depend on one more axiom, `B334.T2.nat_ok._native.native_decide.ax_1_1`.
`#assert_axioms_T2 c` fails unless `c` depends only on `propext`, `Classical.choice`, `Quot.sound` and that one axiom;
any other axiom (`sorryAx`, `Lean.ofReduceBool`, another native-decide axiom, a declared axiom) is a compile error.
The axiom list is logged as information. `#expect_T2_gate_failure c` is the converse, for negative tests: it fails
unless the gate would reject `c`. -/

namespace B334.E1x.AxCheckT2

open Lean Elab Command

/-- the trust base: the three standard axioms and the one T2 native-decide axiom -/
def allowed (a : Name) : Bool :=
  a == ``propext || a == ``Classical.choice || a == ``Quot.sound ||
    a == `B334.T2.nat_ok._native.native_decide.ax_1_1

/-- the axioms of `n` outside the trust base, and all its axioms -/
def outside (n : Name) : CommandElabM (Array Name × Array Name) := do
  let axs ← liftCoreM (collectAxioms n)
  return (axs.filter (fun a => !(allowed a)), axs)

elab "#assert_axioms_T2 " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let (bad, axs) ← outside n
  unless bad.isEmpty do
    throwError "axiom gate (T2): {n} depends on axioms outside the trust base {bad} (all: {axs})"
  logInfo m!"axiom gate (T2): {n} depends on {axs}"

elab "#expect_T2_gate_failure " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let (bad, axs) ← outside n
  if bad.isEmpty then
    throwError "negative test: the T2 gate accepts {n} (axioms {axs}), but it must reject it"
  logInfo m!"negative test: the T2 gate rejects {n} (outside the trust base: {bad})"

end B334.E1x.AxCheckT2
