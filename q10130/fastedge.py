import json, sys
from pathlib import Path
import numpy as np
import run as q

k, eps = 2, 1e-3
model = q.build_model(k, eps)
Y, signs, names = q.initial_batch(k, eps)
pos = signs > 0
Yp, sp = Y[pos], signs[pos]
np_names = [n for n, keep in zip(names, pos) if keep]


def one(theta):
    f = q.factors_adverse(model, theta, 1)
    st = q.solve_group(model, Yp, sp, np_names, f, theta, horizon=8.0)
    return st["passed"] == st["total"], st


def full(theta):
    total = None
    each = {}
    for target in (1, -1):
        f = q.factors_adverse(model, theta, target)
        st = q.solve_group(model, Y, signs, names, f, theta, horizon=8.0)
        each[str(target)] = st
        total = q.merge_stats(total, st, f"fixed-target:{target:+d}")
    return total, each

lo, hi = 0.9 * eps, 1.1 * eps
ok, _ = one(lo)
assert ok
ok, _ = one(hi)
while ok:
    lo, hi = hi, 1.25 * hi
    ok, _ = one(hi)
for _ in range(18):
    mid = (lo + hi) / 2
    ok, _ = one(mid)
    if ok: lo = mid
    else: hi = mid
plo, elo = full(lo)
phi, ehi = full(hi)
assert plo["passed"] == plo["total"]
assert phi["passed"] < phi["total"]
out = dict(k=k, eps=eps,
    definition="symmetry-reduced search; final bracket verified for both fixed mirrored assignments on both signs",
    theta_pass=lo, theta_fail=hi, ratio_pass=lo/eps, ratio_fail=hi/eps,
    pass_stats=plo, fail_stats=phi, pass_by_target=elo, fail_by_target=ehi)
Path(sys.argv[1]).write_text(json.dumps(out, indent=2, sort_keys=True))
