#!/bin/bash
# name_scan.sh LEAN_ROOT LISTFILE: the release name scan for the B334 tree.
# LISTFILE: one module per line (e.g. B334/Tab2/Induct), the modules of the release build (tests excluded).
# Comments (`-- ...` and `/- ... -/` blocks, nested) are removed first, then each LEAN_ROOT/<module>.lean is scanned
# for constructs that could bypass the kernel or hide a gap:
#   FORBIDDEN anywhere: sorry, admit, a top-level `axiom` declaration, implemented_by, extern, unsafe, an `opaque`
#     declaration, addDeclWithoutChecking, unsafeCast, ofReduceBool, trustCompiler, skipKernelTC, and `partial def`
#     outside the loader B334/E1x/Load (whose meta code only reads files at elaboration time; every definition it adds
#     goes through the kernel).
#   ALLOWED ONLY in B334/T2/N_0: native_decide (the one native_decide module, see README).
# Prints one line per hit (module:line:text) and a summary; exit 0 iff 0 hits.
#
# EXEMPTIONS (exact path, each with its reason). They are printed as EXEMPT lines, never
# silently skipped. The arbiter stays the axiom census of the final theorem (the 3 standard axioms plus the allowed
# T2 native axiom, never badAx), and a mechanical check that no module in Final's import closure imports a test.
#   B334/E1x/AxCheckT2Test (whole module): the negative test of the T2 axiom gate. It declares `axiom badAx : 1 = 2`
#     and uses another native_decide ON PURPOSE, so that the gate is seen to reject them. It lives in an isolated
#     test target that the default build and Final's import closure never reach.
#   B334/E1x/AxCheckT2 line 20 only: the gate's allow-list entry, which names the allowed T2 native axiom
#     `B334.T2.nat_ok._native.native_decide.ax_1_1` as a Name literal (no native_decide is run there).
ROOT=${1:?lean root}; LIST=${2:?module list}
exempt_module(){ [ "$1" = "B334/E1x/AxCheckT2Test" ]; }
exempt_line(){ [ "$1" = "B334/E1x/AxCheckT2" ] && [ "$2" = 20 ]; }
[ -d "$ROOT" ] && [ -s "$LIST" ] || { echo "usage: name_scan.sh LEAN_ROOT LISTFILE"; exit 2; }
strip(){ awk '
  { out = ""; i = 1; L = length($0)
    while (i <= L) {
      two = substr($0, i, 2)
      if (depth > 0) {
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "-/") { depth--; i += 2; continue }
        i++; continue }
      if (two == "/-") { depth = 1; i += 2; continue }
      if (two == "--") break
      out = out substr($0, i, 1); i++ }
    print NR ":" out }' "$1"; }
hits=0; n=0
while read -r m; do
  [ -z "$m" ] && continue
  f="$ROOT/$m.lean"; n=$((n+1))
  [ -f "$f" ] || { echo "MISSING $f"; hits=$((hits+1)); continue; }
  if exempt_module "$m"; then echo "EXEMPT $m (whole module: negative test of the T2 axiom gate; see header)"; continue; fi
  pat='\bsorry\b|\badmit\b|^[0-9]+:[[:space:]]*((private|protected|noncomputable)[[:space:]]+)*axiom[[:space:]]|implemented_by|@\[extern|\bunsafe\b|addDeclWithoutChecking|unsafeCast|ofReduceBool|trustCompiler|skipKernelTC|^[0-9]+:[[:space:]]*((private|protected)[[:space:]]+)*opaque[[:space:]]'
  [ "$m" != "B334/E1x/Load" ] && pat="$pat|\\bpartial[[:space:]]+def\\b"
  [ "$m" != "B334/T2/N_0" ] && pat="$pat|native_decide"
  out=$(strip "$f" | command grep -E "$pat")
  if [ -n "$out" ]; then
    while IFS= read -r line; do
      ln=${line%%:*}
      if exempt_line "$m" "$ln"; then echo "EXEMPT $m:$line (allow-list entry naming the approved T2 axiom)"; continue; fi
      echo "HIT $m:$line"; hits=$((hits+1)); done <<< "$out"
  fi
done < "$LIST"
echo "name_scan: modules $n, hits $hits -> $([ $hits = 0 ] && echo PASS || echo FAIL)"
[ $hits = 0 ]
