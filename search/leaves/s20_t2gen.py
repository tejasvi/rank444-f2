#!/usr/bin/env python3
"""s20_t2gen.py OUTDIR --units DIR --stats FILE --p707 FILE --p707-stats FILE --lift DIR: the T2 modules, which put each
completion-leaf certificate on the kernel path or the native path.

Inputs (read only):
  --units DIR    the certificate units of the completion leaves: DIR/C/jobs.txt (lines "c E unitfile", unitfile relative
                 to DIR) and the unit files it lists, as written by gen7_334 --hex (lines "tag nbits hex", each hex a
                 one-leaf batch: bit 0 = 1, then the leaf record R);
  --stats FILE   the per-leaf work statistics of the certificate checker (lines "c tag bits nodes=.. ... outer=..");
  --p707 FILE, --p707-stats FILE
                 the two certificate streams of the leaf of the point search P707R2b and their statistics;
  --lift DIR     the 19 completion leaves of the 10 lifted rows: DIR/lift_c<c>.hex and DIR/lift_stats.txt, keyed by the
                 class id.
Path: K (kernel, `decide +kernel`) if the leaf's b-tries (outer) <= 500, else N (native_decide).
Outputs under OUTDIR:
  t2/manifest.tsv     c, tag, bits, nodes, tries, path, sha256 prefix (16 hex) of the stream's hex text, module;
  t2/plan.tsv         per module: leaves, predicted kernel seconds, predicted maxrss GB;
  t2/layers.txt       the build layers;
  lean/B334/T2/Base.lean, K_<c>_<k>.lean, N_0.lean, Index.lean, Axioms.lean.
Kernel prediction per module (calibrated on eight module builds; every measurement is 61-92% of its
prediction): maxrss GB = 0.46 + 0.0010 * (sum of b-tries) + 0.0025 * (leaves) + 0.0010 * (sum of nodes) + 0.006 * (max
b-tries); seconds = 0.03 * (sum of b-tries) + 0.05 * (leaves).  (Memory is partly retained between the declarations of a
module; the running leaf adds about 4-7 MB per b-try.  Measured (leaves, tries, max tries, nodes: GB, s): 42, 5873, 471,
1371: 7.71, 155; 67, 3140, 252, 537: 5.09, 59; 500, 4551, 181, 715: 6.37, 34; 2, 597, 428, 40: 2.90, 31; 468, 4315,
92, 738: 6.34, 35; 33, 3043, 485, 641: 5.03, 75; 248, 3626, 299, 1438: 7.30, 77; 25, 3141, 455, 1072: 4.58, 74.)
K modules: per plane, consecutive leaves, at most 500 leaves and a predicted maxrss of at most 7.0 GB each (the -M 7600
rule).
"""
import argparse
import hashlib
import os

LIFT_CLS = [27, 291, 30, 301, 31, 40, 59, 81, 84, 90]
NLEAVES = 19543 + 19
TRY_K = 500
MAX_LEAVES, MEM_MAX = 500, 7.0


def t_pred(ls):
    return 0.03 * sum(l[4] for l in ls) + 0.05 * len(ls)


def m_pred(ls):
    return 0.46 + 0.0010 * sum(l[4] for l in ls) + 0.0025 * len(ls) + 0.0010 * sum(l[3] for l in ls) + \
        0.006 * max(l[4] for l in ls)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('out')
    for o in ('--units', '--stats', '--p707', '--p707-stats', '--lift'):
        ap.add_argument(o, required=True)
    a = ap.parse_args()
    out, STATS, LIFT = a.out, a.stats, a.lift
    for d in ('t2', 'lean/B334/T2'):
        os.makedirs(os.path.join(out, d), exist_ok=False)
    stats = {}
    for line in list(open(STATS)) + list(open(a.p707_stats)) + list(open(LIFT + '/lift_stats.txt')):
        f = line.split()
        if len(f) < 4 or f[2] == 'REJECT':
            continue
        kv = dict(w.split('=') for w in f[3:] if '=' in w)
        stats[(int(f[0]), f[1])] = (int(f[2]), int(kv['nodes']), int(kv['outer']))
    leaves = []                               # (c, tag, bits, nodes, tries, hex, R)
    seen = set()
    srcs = [(int(c), os.path.join(a.units, h)) for c, E, h in (l.split() for l in open(os.path.join(a.units, 'C', 'jobs.txt')))]
    srcs.append((707, a.p707))
    srcs += [(c, '%s/lift_c%d.hex' % (LIFT, c)) for c in LIFT_CLS]
    for c, path in srcs:
        for line in open(path):
            tag, nb, hx = line.split()
            tag = tag.rstrip(':')
            S = int(hx, 16)
            assert S & 1 == 1 and S >> int(nb) == 0, (c, tag)
            key = (c, tag)
            assert key not in seen, key
            seen.add(key)
            bits, nodes, tries = stats[key]
            assert bits == int(nb), (key, bits, nb)
            leaves.append((c, tag, bits, nodes, tries, hx.lower(), S >> 1))
    assert len(leaves) == NLEAVES, len(leaves)
    planes = sorted(set(l[0] for l in leaves))
    # ---- K modules
    kmods = []                                 # (name, c, [leaves])
    modof = {}
    for c in planes:
        cur, k = [], 0
        for l in (x for x in leaves if x[0] == c and x[4] <= TRY_K):
            if cur and (len(cur) >= MAX_LEAVES or m_pred(cur + [l]) > MEM_MAX):
                kmods.append(('K_%d_%d' % (c, k), c, cur))
                cur, k = [], k + 1
            cur.append(l)
        if cur:
            kmods.append(('K_%d_%d' % (c, k), c, cur))
    for name, c, ls in kmods:
        for l in ls:
            modof[(l[0], l[1])] = name
    nat = [l for l in leaves if l[4] > TRY_K]
    for l in nat:
        modof[(l[0], l[1])] = 'N_0'
    hdr = ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 0', '']
    T2 = os.path.join(out, 'lean/B334/T2')

    def chain(names_ok, nil='all_nil'):
        s = nil
        for n in reversed(names_ok):
            s = 'all_cons %s (%s)' % (n, s)
        return s
    # ---- Base
    B = ['import B334.BC.BranchCheck334', '',
         '/-! # T2: helpers for lists of accepted leaf records. GENERATED by a script; do not edit. -/', '',
         'namespace B334.T2', 'open B334.BC', '',
         'theorem all_nil : ∀ R ∈ ([] : List Nat), leafS R = true := fun _ h => nomatch h',
         'theorem all_cons {a : Nat} {l : List Nat} (ha : leafS a = true) (hl : ∀ R ∈ l, leafS R = true) :',
         '    ∀ R ∈ a :: l, leafS R = true := List.forall_mem_cons.mpr ⟨ha, hl⟩',
         'theorem all_append {l₁ l₂ : List Nat} (h₁ : ∀ R ∈ l₁, leafS R = true) (h₂ : ∀ R ∈ l₂, leafS R = true) :',
         '    ∀ R ∈ l₁ ++ l₂, leafS R = true := fun R hR => (List.mem_append.mp hR).elim (h₁ R) (h₂ R)',
         'theorem all_of_all {l : List Nat} (h : l.all leafS = true) : ∀ R ∈ l, leafS R = true :=',
         '  fun R hR => List.all_eq_true.mp h R hR',
         'theorem and_left (a b : Bool) (h : (a && b) = true) : a = true := by',
         '  cases a',
         '  · simp at h',
         '  · rfl',
         'theorem and_right (a b : Bool) (h : (a && b) = true) : b = true := by',
         '  cases a',
         '  · simp at h',
         '  · simpa using h', '', 'end B334.T2']
    open(os.path.join(T2, 'Base.lean'), 'w').write('\n'.join(B) + '\n')
    plan = []
    for name, c, ls in kmods:
        W = ['import B334.T2.Base', ''] + hdr + [
            '/-! # T2 kernel leaves of plane %d, part %s (%d leaves). GENERATED by a script; do not edit. -/' % (
                c, name.rsplit('_', 1)[1], len(ls)), '', 'namespace B334.T2', 'open B334.BC', '']
        for l in ls:
            W += ['def L_%d_%s : Nat := 0x%x' % (c, l[1], l[6]),
                  'theorem k_%d_%s : leafS L_%d_%s = true := by decide +kernel' % (c, l[1], c, l[1])]
        lname = 'kl_%s' % name[2:]
        W += ['', 'def %s : List Nat := [%s]' % (lname, ', '.join('L_%d_%s' % (c, l[1]) for l in ls)),
              'theorem %s_ok : ∀ R ∈ %s, leafS R = true :=' % (lname, lname),
              '  ' + chain(['k_%d_%s' % (c, l[1]) for l in ls]), '', 'end B334.T2']
        open(os.path.join(T2, name + '.lean'), 'w').write('\n'.join(W) + '\n')
        plan.append((name, len(ls), t_pred(ls), m_pred(ls)))
    # ---- N_0
    nplanes = sorted(set(l[0] for l in nat))
    W = ['import B334.T2.Base', ''] + hdr + [
        '/-! # T2 native leaves (%d leaves with more than %d b-tries). GENERATED by a script; do not edit.' % (len(nat), TRY_K),
        '', 'One `native_decide` theorem (one axiom) checks every leaf record with `leafS`; the per-plane facts follow. -/',
        '', 'namespace B334.T2', 'open B334.BC', '']
    for l in nat:
        W.append('def L_%d_%s : Nat := 0x%x' % (l[0], l[1], l[6]))
    for c in nplanes:
        W.append('def nl_%d : List Nat := [%s]' % (c, ', '.join('L_%d_%s' % (c, l[1]) for l in nat if l[0] == c)))
    conj = 'true'
    for c in reversed(nplanes):
        conj = '(nl_%d.all leafS && %s)' % (c, conj)
    W += ['', 'theorem nat_ok : %s = true := by native_decide' % conj, '']
    for i, c in enumerate(nplanes):
        t = 'nat_ok'
        for _ in range(i):
            t = '(and_right _ _ %s)' % t
        W.append('theorem nl_%d_ok : ∀ R ∈ nl_%d, leafS R = true := all_of_all (and_left _ _ %s)' % (c, c, t))
    W += ['', 'end B334.T2']
    open(os.path.join(T2, 'N_0.lean'), 'w').write('\n'.join(W) + '\n')
    # ---- Index
    I = ['import B334.T2.%s' % name for name, _, _ in kmods] + ['import B334.T2.N_0', ''] + hdr[:1] + [
        '', '/-! # T2 index: per plane, the accepted leaf records and their `leafS` facts. GENERATED by a script.',
        '', '`leaves_c` lists the leaf records `R` of plane `c` (707: P707R2b); `ok_c : ∀ R ∈ leaves_c, leafS R = true`.',
        'Lookup key for a leaf: the header, the low 520 + 9n bits of R (n, the n labels, dom mode 01, the dom mask); the',
        'certificate is `R >>> (520 + 9n)`. -/', '', 'namespace B334.T2', 'open B334.BC', '']
    for c in planes:
        parts = [('kl_%s' % name[2:], 'kl_%s_ok' % name[2:]) for name, cc, _ in kmods if cc == c]
        if c in nplanes:
            parts.append(('nl_%d' % c, 'nl_%d_ok' % c))
        lst, prf = '[]', 'all_nil'
        for a, b in reversed(parts):
            lst = '%s ++ (%s)' % (a, lst)
            prf = 'all_append %s (%s)' % (b, prf)
        I += ['def leaves_%d : List Nat := %s' % (c, lst),
              'theorem ok_%d : ∀ R ∈ leaves_%d, leafS R = true := %s' % (c, c, prf)]
    I += ['', 'end B334.T2']
    open(os.path.join(T2, 'Index.lean'), 'w').write('\n'.join(I) + '\n')
    A = ['import B334.T2.Index', '', '/-! # T2 axiom census (not part of the library). GENERATED by a script. -/', '']
    A += ['#print axioms B334.T2.nat_ok'] + ['#print axioms B334.T2.kl_%s_ok' % name[2:] for name, _, _ in kmods]
    A += ['#print axioms B334.T2.ok_%d' % c for c in planes]
    open(os.path.join(T2, 'Axioms.lean'), 'w').write('\n'.join(A) + '\n')
    # ---- manifest, plan, layers
    with open(os.path.join(out, 't2/manifest.tsv'), 'w') as f:
        f.write('c\ttag\tbits\tnodes\ttries\tpath\tsha256_16\tmodule\n')
        for l in leaves:
            f.write('%d\t%s\t%d\t%d\t%d\t%s\t%s\t%s\n' % (l[0], l[1], l[2], l[3], l[4], 'K' if l[4] <= TRY_K else 'N',
                                                         hashlib.sha256(l[5].encode()).hexdigest()[:16], modof[(l[0], l[1])]))
    with open(os.path.join(out, 't2/plan.tsv'), 'w') as f:
        f.write('module\tleaves\tpred_s\tpred_maxrss_gb\n')
        for name, n, s, m in plan:
            f.write('%s\t%d\t%.1f\t%.2f\n' % (name, n, s, m))
    with open(os.path.join(out, 't2/layers.txt'), 'w') as f:
        f.write('B334/BC/Tables334\nB334/BC/BranchCheck334\nB334/T2/Base\n')
        f.write(' '.join(['B334/T2/N_0'] + ['B334/T2/%s' % name for name, _, _ in kmods]) + '\n')
        f.write('B334/T2/Index\nB334/T2/Axioms\n')
    nk = sum(len(ls) for _, _, ls in kmods)
    print('s20_t2gen: %d leaves (%d K in %d modules, %d N); %d planes; predicted K: %.0f core-s total, max module %.0f s, '
          'max module maxrss %.2f GB' % (len(leaves), nk, len(kmods), len(nat), len(planes), sum(p[2] for p in plan),
                                       max(p[2] for p in plan), max(p[3] for p in plan)))


if __name__ == '__main__':
    main()
