#!/usr/bin/env python3
"""Emit the equal-cost re-shard of the Round-82 C5 kernel.

    emit_c5_reshard.py REPO [--shards 21] [--check] [--print-bounds]

The six original shards of the development repository split `t : Fin 126` into
equal ranges, but the cost of deciding `ClearedC5At t` grows linearly in `t` (measured on a
cold build: 486, 893, 1376, 1865, 2340, 2786 CPU-s for the six ranges of 21).  This
emitter fits cost(t) = a + b*t by least squares to those six numbers, and cuts [0, 126) into
`--shards` integer ranges minimising the largest fitted cost (t_i ~ 126*sqrt(i/n) for a linear
cost, corrected for the intercept and for integer granularity).

Emitted, all under OmegaBound/:
  ADVXXZT6Round82C5KernelK{i}.lean   one `native_decide` each, i = 0 .. n-1
  ADVXXZT6Round82C5KernelChecked.lean  the n-way case split; its theorem statement is unchanged.
`--check` compares byte for byte instead of writing.
"""

from __future__ import annotations

import argparse
import math
import pathlib
import sys

MEASURED_CPU_S = [485.81, 892.87, 1375.61, 1865.16, 2339.91, 2786.39]  # rc5cold-sampler.json
OLD_WIDTH = 21
N_T = 126


def fit() -> tuple[float, float]:
    # shard k sum = 21 a + b * sum_{t=21k}^{21k+20} t = 21 a + b * (441 k + 210)
    xs = [(OLD_WIDTH, OLD_WIDTH * OLD_WIDTH * k + OLD_WIDTH * (OLD_WIDTH - 1) / 2) for k in range(6)]
    # normal equations for [a, b]
    s11 = sum(x[0] * x[0] for x in xs)
    s12 = sum(x[0] * x[1] for x in xs)
    s22 = sum(x[1] * x[1] for x in xs)
    r1 = sum(x[0] * y for x, y in zip(xs, MEASURED_CPU_S))
    r2 = sum(x[1] * y for x, y in zip(xs, MEASURED_CPU_S))
    det = s11 * s22 - s12 * s12
    return (r1 * s22 - r2 * s12) / det, (s11 * r2 - s12 * r1) / det


def bounds(n: int) -> list[int]:
    """Integer cut points minimising the largest fitted shard cost (greedy packing under a cap,
    cap found by bisection)."""
    a, b = fit()
    cost = lambda t: a + b * t

    def pack(cap: float) -> list[int] | None:
        cuts, acc = [0], 0.0
        for t in range(N_T):
            if cost(t) > cap:
                return None
            if acc + cost(t) > cap:
                cuts.append(t)
                acc = 0.0
            acc += cost(t)
        cuts.append(N_T)
        return cuts if len(cuts) - 1 <= n else None

    lo, hi = 0.0, sum(cost(t) for t in range(N_T))
    for _ in range(100):
        mid = (lo + hi) / 2
        lo, hi = (lo, mid) if pack(mid) else (mid, hi)
    cuts = pack(hi)
    assert cuts is not None and len(cuts) - 1 == n, cuts
    assert all(x < y for x, y in zip(cuts, cuts[1:])), cuts
    return cuts


def shard_module(i: int, lo: int, hi: int, n: int) -> str:
    guards = []
    if lo > 0:
        guards.append(f"{lo} <= t.1 -> ")
    if hi < N_T:
        guards.append(f"t.1 < {hi} -> ")
    return (
        "import OmegaBound.ADVXXZT6Round82C5Kernel\n"
        "namespace OmegaBound.ADVXXZT6Round82\n"
        f"/-- Equal-cost C5 shard {i} of {n}: parents {lo} <= t < {hi} "
        "(emitted by `release/emitters/emit_c5_reshard.py`). -/\n"
        f"def C5ShardK{i} : Prop := forall t : Fin 126, {''.join(guards)}ClearedC5At t\n"
        f"instance : Decidable C5ShardK{i} := by unfold C5ShardK{i}; infer_instance\n"
        f"set_option maxHeartbeats 8000000 in theorem c5ShardK{i} : C5ShardK{i} := by native_decide\n"
        "end OmegaBound.ADVXXZT6Round82\n"
    )


def checked_module(cuts: list[int]) -> str:
    n = len(cuts) - 1
    out = [f"import OmegaBound.ADVXXZT6Round82C5KernelK{i}\n" for i in range(n)]
    out.append("namespace OmegaBound.ADVXXZT6Round82\n")
    out.append(
        f"/-- All 126 parents and all three physical rows, assembled from {n} equal-cost "
        "cleared-integer shards. -/\n"
    )
    out.append("theorem released_cleared_C5 (t : Fin 126) : ClearedC5At t := by\n")
    for i in range(n - 1):
        hi = cuts[i + 1]
        out.append(f"  by_cases h{i} : t.1 < {hi}\n")
        if i == 0:
            out.append(f"  · exact c5ShardK0 t h0\n")
        else:
            out.append(f"  · exact c5ShardK{i} t (by omega) h{i}\n")
    out.append(f"  · exact c5ShardK{n - 1} t (by omega)\n")
    out.append("end OmegaBound.ADVXXZT6Round82\n")
    return "".join(out)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo")
    ap.add_argument("--shards", type=int, default=21)
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--print-bounds", action="store_true")
    args = ap.parse_args()
    cuts = bounds(args.shards)
    if args.print_bounds:
        a, b = fit()
        cum = lambda T: a * T + b * T * (T - 1) / 2
        print(f"fit: cost(t) = {a:.3f} + {b:.4f} t CPU-s; total {cum(N_T):.0f} CPU-s")
        for i in range(args.shards):
            lo, hi = cuts[i], cuts[i + 1]
            print(f"K{i:<2} [{lo:3}, {hi:3})  width {hi - lo:2}  fitted {cum(hi) - cum(lo):6.0f} CPU-s"
                  f"  sqrt-rule lo {126 * math.sqrt(i / args.shards):6.1f}")
    files = {f"ADVXXZT6Round82C5KernelK{i}.lean": shard_module(i, cuts[i], cuts[i + 1], args.shards)
             for i in range(args.shards)}
    files["ADVXXZT6Round82C5KernelChecked.lean"] = checked_module(cuts)
    root = pathlib.Path(args.repo) / "OmegaBound"
    bad = 0
    for name, text in files.items():
        p = root / name
        if args.check:
            if not p.exists() or p.read_text() != text:
                print(f"DIFFERS {name}", file=sys.stderr)
                bad += 1
        else:
            p.write_text(text)
    if args.check:
        print(f"check: {len(files) - bad}/{len(files)} identical")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
