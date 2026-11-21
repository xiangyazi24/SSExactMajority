import json, sys
from pathlib import Path
import numpy as np
import run as q


def run_mode(k, ei, mi, outpath):
    eps = q.EPS[ei]
    name = q.THETA_NAMES[mi]
    theta = q.theta_values(k, eps)[name]
    model = q.build_model(k, eps)
    Y0, signs, names = q.initial_batch(k, eps)
    rng = np.random.default_rng(101300000 + 10000 * k + 100 * ei)
    U = rng.uniform(-1.0, 1.0, size=(q.N_RATE_ASSIGNMENTS, model["channels"]))
    rand = None
    for rid in range(q.N_RATE_ASSIGNMENTS):
        st = q.solve_group(model, Y0, signs, names, np.exp(theta * U[rid]), theta)
        rand = q.merge_stats(rand, st, f"random:{rid}")
    nominal = None
    if mi == 0:
        nominal = q.solve_group(model, Y0, signs, names, np.ones(model["channels"]), 0.0)
    ans = dict(k=k, eps=eps, mode=name, theta=theta, random=rand, nominal=nominal,
               channels=model["channels"], duplicates=model["duplicates"],
               starts_per_sign=len(Y0) // 2)
    Path(outpath).write_text(json.dumps(ans, indent=2, sort_keys=True))


def aggregate(indir, outpath, reportpath):
    rows = [json.loads(p.read_text()) for p in sorted(Path(indir).glob("split-*.json"))]
    cells = {}
    for r in rows:
        key = (r["k"], r["eps"])
        c = cells.setdefault(key, dict(k=r["k"], eps=r["eps"], channels=r["channels"],
                                       duplicates=r["duplicates"], starts_per_sign=r["starts_per_sign"],
                                       nominal=None, theta={}))
        c["theta"][r["mode"]] = dict(theta=r["theta"], random=r["random"])
        if r["nominal"] is not None: c["nominal"] = r["nominal"]
    out = dict(cells=[cells[k] for k in sorted(cells)], random_starts=q.N_RANDOM_STARTS,
               rate_assignments=q.N_RATE_ASSIGNMENTS, rtol=q.RTOL, atol=q.ATOL)
    Path(outpath).write_text(json.dumps(out, indent=2, sort_keys=True))
    with open(reportpath, "w") as f:
        for c in sorted(out["cells"], key=lambda z: (z["k"], -z["eps"])):
            n = c["nominal"]
            print("SPLIT_CELL", c["k"], c["eps"], c["starts_per_sign"], c["channels"],
                  n["passed"], n["total"], n["worst_entry"], n["worst_name"],
                  n["min_final_signed_h"], file=f)
            for name, v in sorted(c["theta"].items()):
                r = v["random"]
                print("SPLIT_MODE", c["k"], c["eps"], name, v["theta"], r["passed"],
                      r["total"], r["worst_entry"], r["worst_name"], r["worst_rate"],
                      r["min_final_signed_h"], file=f)


if __name__ == "__main__":
    if sys.argv[1] == "mode": run_mode(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    elif sys.argv[1] == "aggregate": aggregate(sys.argv[2], sys.argv[3], sys.argv[4])
