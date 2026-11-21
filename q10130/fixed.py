import json, sys
from pathlib import Path
import numpy as np
import run as q


def merge(acc, cur, tag):
    return q.merge_stats(acc, cur, tag)


def fixed_stats(k, eps, theta, horizon=2.0):
    model = q.build_model(k, eps)
    Y0, signs, names = q.initial_batch(k, eps)
    total = None
    each = {}
    for target in (1, -1):
        factors = q.factors_adverse(model, theta, target)
        st = q.solve_group(model, Y0, signs, names, factors, theta, horizon=horizon)
        each[str(target)] = st
        total = merge(total, st, f"fixed-target:{target:+d}")
    return total, each


def run_cell(k, ei, outpath):
    eps = q.EPS[ei]
    model = q.build_model(k, eps)
    ans = dict(k=k, eps=eps, starts_per_sign=len(q.initial_batch(k, eps)[0]) // 2,
               channels=model["channels"], duplicates=model["duplicates"], theta={})
    for name, theta in q.theta_values(k, eps).items():
        total, each = fixed_stats(k, eps, theta)
        ans["theta"][name] = dict(theta=theta, adverse=total, by_target=each)
    Path(outpath).write_text(json.dumps(ans, indent=2, sort_keys=True))


def all_pass(k, eps, theta):
    total, each = fixed_stats(k, eps, theta, horizon=8.0)
    return total["passed"] == total["total"], total, each


def run_edge(outpath):
    k, eps = 2, 1e-3
    lo, hi = 0.0, 0.1 * eps
    ok, total, each = all_pass(k, eps, hi)
    while ok and hi < 1.0:
        lo, hi = hi, 2 * hi
        ok, total, each = all_pass(k, eps, hi)
    assert not ok
    for _ in range(24):
        mid = (lo + hi) / 2
        ok, total, each = all_pass(k, eps, mid)
        if ok: lo = mid
        else: hi = mid
    _, plo, elo = all_pass(k, eps, lo)
    _, phi, ehi = all_pass(k, eps, hi)
    ans = dict(k=k, eps=eps,
               definition="two fixed sign-mirrored assignments, each unchanged across both input signs",
               theta_pass=lo, theta_fail=hi, ratio_pass=lo / eps, ratio_fail=hi / eps,
               pass_stats=plo, fail_stats=phi, pass_by_target=elo, fail_by_target=ehi)
    Path(outpath).write_text(json.dumps(ans, indent=2, sort_keys=True))


def aggregate(indir, outpath, reportpath):
    cells = [json.loads(p.read_text()) for p in sorted(Path(indir).glob("fixed-cell-*.json"))]
    edge = json.loads((Path(indir) / "fixed-edge.json").read_text())
    out = dict(cells=cells, edge=edge)
    Path(outpath).write_text(json.dumps(out, indent=2, sort_keys=True))
    with open(reportpath, "w") as f:
        print("FIXED_EDGE", json.dumps(edge, sort_keys=True), file=f)
        for c in sorted(cells, key=lambda z: (z["k"], -z["eps"])):
            for name, v in sorted(c["theta"].items()):
                a = v["adverse"]
                print("FIXED", c["k"], c["eps"], name, v["theta"], a["passed"], a["total"],
                      a["worst_entry"], a["worst_name"], a["worst_rate"],
                      a["min_final_signed_h"], file=f)


if __name__ == "__main__":
    if sys.argv[1] == "cell": run_cell(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    elif sys.argv[1] == "edge": run_edge(sys.argv[2])
    elif sys.argv[1] == "aggregate": aggregate(sys.argv[2], sys.argv[3], sys.argv[4])
