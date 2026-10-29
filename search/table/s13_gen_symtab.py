#!/usr/bin/env python3
"""s13_gen_symtab.py OUT_LEAN OUT_TSV : the pair-symmetry tables for <3,3,4>.

Encodings (as in B334/Core/SymBits.lean):
  S (4x4): bit 4r+c;  b (3x4): bit 4j+k;  c (4x3): bit 3k+i.  Action: (b, c) -> (b S, S^-1 c).
Tables:
  ORBM      the 15 orbit minima of B\\{0} under b -> b S, S in GL4(F2) (one per column space in F2^3);
  WB[b]     for every nonzero b: (S, S^-1) with b S in ORBM;
  CORB[o]   for each o in ORBM: the minima of the orbits of C\\{0} under c -> S^-1 c, S in Stab(o) = {S : o S = o};
  WC[o][c]  for every nonzero c: (S, S^-1) with S in Stab(o) and S^-1 c in CORB[o].
Every table entry is re-checked here (S S^-1 = I, the orbit and stabilizer conditions); the Lean file re-checks them by
`decide +kernel`.  Orbits use generating sets (12 transvections for GL4; for Stab(o) a set whose closure is all of
Stab(o), checked by size), so CORB[o] holds exactly the minima of the full Stab(o)-orbits.
"""
import sys

ID44 = 0x8421


def rows(m, nr, w):
    return [(m >> (w * r)) & ((1 << w) - 1) for r in range(nr)]


def from_rows(rs, w):
    v = 0
    for r, x in enumerate(rs):
        v |= x << (w * r)
    return v


def mul44(u, v):
    vr = rows(v, 4, 4)
    out = []
    for ur in rows(u, 4, 4):
        acc = 0
        for l in range(4):
            if (ur >> l) & 1:
                acc ^= vr[l]
        out.append(acc)
    return from_rows(out, 4)


def mulBS(b, S):
    Sr = rows(S, 4, 4)
    out = []
    for br in rows(b, 3, 4):
        acc = 0
        for l in range(4):
            if (br >> l) & 1:
                acc ^= Sr[l]
        out.append(acc)
    return from_rows(out, 4)


def mulSC(S, c):
    cr = rows(c, 4, 3)
    out = []
    for Sr in rows(S, 4, 4):
        acc = 0
        for l in range(4):
            if (Sr >> l) & 1:
                acc ^= cr[l]
        out.append(acc)
    return from_rows(out, 3)


def inv44(S):
    a = rows(S, 4, 4)
    e = rows(ID44, 4, 4)
    for col in range(4):
        piv = next((r for r in range(col, 4) if (a[r] >> col) & 1), None)
        if piv is None:
            return None
        a[col], a[piv] = a[piv], a[col]
        e[col], e[piv] = e[piv], e[col]
        for r in range(4):
            if r != col and (a[r] >> col) & 1:
                a[r] ^= a[col]
                e[r] ^= e[col]
    return from_rows(e, 4)


def main():
    out_lean, out_tsv = sys.argv[1], sys.argv[2]
    gl4 = [S for S in range(1 << 16) if inv44(S) is not None]
    assert len(gl4) == 20160, len(gl4)
    inv = {S: inv44(S) for S in gl4}
    for S in gl4:
        assert mul44(S, inv[S]) == ID44 and mul44(inv[S], S) == ID44
    trans = [ID44 ^ (1 << (4 * i + j)) for i in range(4) for j in range(4) if i != j]
    assert all(t in inv and inv[t] == t for t in trans)
    # ---- ORBM and WB: BFS from each orbit minimum o with M_x such that o M_x = x; then WB[x] = (M_x^-1, M_x)
    wb = [None] * 4096
    orbm = []
    for b0 in range(1, 4096):
        if wb[b0] is not None:
            continue
        o = b0                       # smallest unvisited: the minimum of its orbit
        orbm.append(o)
        M = {o: ID44}
        queue = [o]
        for x in queue:
            for g in trans:
                y = mulBS(x, g)
                if y not in M:
                    M[y] = mul44(M[x], g)
                    queue.append(y)
        assert min(M) == o
        for x, Mx in M.items():
            assert mulBS(o, Mx) == x
            wb[x] = (inv[Mx], Mx)
    assert len(orbm) == 15, orbm
    for b in range(1, 4096):
        S, Si = wb[b]
        assert mul44(S, Si) == ID44 and mulBS(b, S) in orbm
    # ---- CORB and WC
    corb, wc, stabsz = {}, {}, {}
    for o in orbm:
        stab = [S for S in gl4 if mulBS(o, S) == o]
        stabsz[o] = len(stab)
        gens, closure = [], {ID44}
        for S in stab:
            if S in closure:
                continue
            gens.append(S)
            gens_all = gens + [inv[g] for g in gens]
            closure = {ID44}
            queue = [ID44]
            for x in queue:
                for g in gens_all:
                    y = mul44(x, g)
                    if y not in closure:
                        closure.add(y)
                        queue.append(y)
        assert closure == set(stab), (o, len(closure), len(stab))
        gens_all = gens + [inv[g] for g in gens]
        w = [None] * 4096
        mins = []
        for c0 in range(1, 4096):
            if w[c0] is not None:
                continue
            m = c0
            mins.append(m)
            N = {m: ID44}            # N_x m = x, N_x in Stab(o)
            queue = [m]
            for x in queue:
                for g in gens_all:
                    y = mulSC(g, x)
                    if y not in N:
                        N[y] = mul44(g, N[x])
                        queue.append(y)
            assert min(N) == m
            for x, Nx in N.items():
                assert mulSC(Nx, m) == x
                w[x] = (Nx, inv[Nx])  # S = N_x in Stab(o), S^-1 x = m
        for c in range(1, 4096):
            S, Si = w[c]
            assert mul44(S, Si) == ID44 and mulBS(o, S) == o and mulSC(Si, c) in mins
        corb[o], wc[o] = mins, w
    # ---- write the TSV (for the C++ cross-check) and the Lean tables
    with open(out_tsv, 'w') as f:
        f.write('# kind\tkey\tvalue (S and S^-1 as 16-bit masks; b, c as 12-bit masks)\n')
        f.write('ORBM\t-\t%s\n' % ','.join(map(str, orbm)))
        for o in orbm:
            f.write('STAB\t%d\t%d\n' % (o, stabsz[o]))
            f.write('CORB\t%d\t%s\n' % (o, ','.join(map(str, corb[o]))))
        for b in range(1, 4096):
            f.write('WB\t%d\t%d,%d\n' % (b, wb[b][0], wb[b][1]))
        for o in orbm:
            for c in range(1, 4096):
                f.write('WC\t%d:%d\t%d,%d\n' % (o, c, wc[o][c][0], wc[o][c][1]))

    def mask(bits):
        v = 0
        for x in bits:
            v |= 1 << x
        return v

    def packed(entries):
        v = 0
        for i, e in enumerate(entries):
            if e is not None:
                v |= (e[0] | (e[1] << 16)) << (32 * i)
        return v

    L = []
    L.append('import B334.Core.SymBits')
    L.append('')
    L.append('/-! # Pair-symmetry tables for ⟨3,3,4⟩. GENERATED by a script; do not edit.')
    L.append('')
    L.append('- `ORBM`: the 15 orbit minima of the nonzero 3×4 matrices `b` under `b ↦ b S`, `S ∈ GL₄(F₂)`.')
    L.append('- `WB`: for every nonzero `b`, a pair `(S, S⁻¹)` (bits 32b … 32b+31: `S`, then `S⁻¹`) with `b S ∈ ORBM`.')
    L.append('- `CORB_o`: for each `o ∈ ORBM`, the minima of the orbits of the nonzero 4×3 matrices `c` under `c ↦ S⁻¹ c`,')
    L.append('  `S ∈ Stab(o)`; `WC_o`: for every nonzero `c`, `(S, S⁻¹)` with `o S = o` and `S⁻¹ c ∈ CORB_o`.')
    L.append('')
    L.append('The facts are kernel checks (`decide +kernel`); they need no list of all of GL₄(F₂): each entry carries its')
    L.append('inverse, which is checked. Stabilizer sizes: %s. -/' % ', '.join('%d: %d' % (o, stabsz[o]) for o in orbm))
    L.append('')
    L.append('namespace B334.Tab')
    L.append('open B334.Core')
    L.append('')
    L.append('/-- the 15 orbit minima (`ORBL`) as a 4096-bit mask -/')
    L.append('def ORBM : Nat := 0x%x' % mask(orbm))
    L.append('def ORBL : List Nat := [%s]' % ', '.join(map(str, orbm)))
    L.append('def WB : Nat := 0x%x' % packed(wb))
    L.append('/-- entry `i` of a packed table: `S` -/')
    L.append('def pS (T i : Nat) : Nat := (T >>> (32 * i)) &&& 65535')
    L.append('/-- entry `i` of a packed table: `S⁻¹` -/')
    L.append('def pSi (T i : Nat) : Nat := (T >>> (32 * i + 16)) &&& 65535')
    for o in orbm:
        L.append('def CORB_%d : Nat := 0x%x' % (o, mask(corb[o])))
        L.append('def WC_%d : Nat := 0x%x' % (o, packed(wc[o])))
    L.append('')
    L.append('/-- `CORB o` for `o ∈ ORBL` (0 otherwise) -/')
    L.append('def CORB (o : Nat) : Nat :=')
    for o in orbm:
        L.append('  if o = %d then CORB_%d else' % (o, o))
    L.append('  0')
    L.append('/-- `WC o` for `o ∈ ORBL` (0 otherwise) -/')
    L.append('def WC (o : Nat) : Nat :=')
    for o in orbm:
        L.append('  if o = %d then WC_%d else' % (o, o))
    L.append('  0')
    L.append('')
    L.append('/-- the `WB` check for one `b` -/')
    L.append('def wbOK (b : Nat) : Bool := b == 0 || (mul44 (pS WB b) (pSi WB b) == 33825 && ORBM.testBit (mulBS b (pS WB b)))')
    L.append('/-- the `WC` check for one orbit minimum `o`: every nonzero `c` has `(S, S⁻¹)` with `S S⁻¹ = I`, `o S = o`, `S⁻¹ c ∈ CORB_o` -/')
    L.append('def wcOK (o W C : Nat) : Bool := allLT 4096 (fun c => c == 0 ||')
    L.append('  (mul44 (pS W c) (pSi W c) == 33825 && mulBS o (pS W c) == o && C.testBit (mulSC (pSi W c) c)))')
    L.append('')
    L.append('end B334.Tab')
    with open(out_lean, 'w') as f:
        f.write('\n'.join(L) + '\n')
    # kernel facts: one module per fact group, so they build in parallel (same-module decide theorems run serially);
    # maxRecDepth/maxHeartbeats as options (a decide failure can hide a heartbeat timeout)
    base = out_lean[:-len('.lean')]
    hdr = ['set_option maxRecDepth 1000000', 'set_option maxHeartbeats 0', '']
    def facts_module(path, title, thms):
        W = ['import B334.Tables.SymTab', ''] + hdr + [
             '/-! # %s. GENERATED by a script; do not edit. -/' % title, '',
             'namespace B334.Tab', 'open B334.Core', ''] + thms + ['', 'end B334.Tab']
        with open(path, 'w') as f:
            f.write('\n'.join(W) + '\n')
    facts_module(base + 'Orb.lean', 'Kernel facts: `ORBM` = `ORBL`, and the witness table `WB`', [
        '/-- `ORBM` has exactly the bits `ORBL` -/',
        'theorem orbm_fact : allLT 4096 (fun v => ORBM.testBit v == ORBL.contains v) = true := by decide +kernel',
        '/-- every nonzero `b` has a listed `(S, S⁻¹)`, `S S⁻¹ = I`, with `b S ∈ ORBM` -/',
        'theorem wb_fact : allLT 4096 wbOK = true := by decide +kernel'])
    for o in orbm:
        facts_module(base + 'WC_%d.lean' % o, '`WC` kernel fact for the orbit minimum %d' % o, [
            'theorem wc_fact_%d : wcOK %d WC_%d CORB_%d = true := by decide +kernel' % (o, o, o, o)])
    with open(base + 'WC.lean', 'w') as f:
        f.write('\n'.join(['import B334.Tables.SymTabOrb'] + ['import B334.Tables.SymTabWC_%d' % o for o in orbm] + [
            '', '/-! # All kernel facts of the witness tables `WB` and `WC` (aggregator). GENERATED by a script; do not edit. -/']) + '\n')
    print('wrote', base + 'Orb.lean', base + 'WC_<o>.lean (15)', base + 'WC.lean')
    print('ORBM', orbm)
    print('stab sizes', [stabsz[o] for o in orbm], 'CORB sizes', [len(corb[o]) for o in orbm])
    print('wrote', out_lean, out_tsv)


if __name__ == '__main__':
    main()
