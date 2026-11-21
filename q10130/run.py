import json, math, sys
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

EPS = [1e-2, 3e-3, 1e-3, 3e-4]
THETA_NAMES = ["ck", "10ck", "100ck", "0.1eps"]
N_RANDOM_STARTS = 50
N_RATE_ASSIGNMENTS = 25
RTOL = 1e-9
ATOL = 1e-12


def lab(i, s):
    return 2 * i - 1 if s > 0 else 2 * i


def build_model(k, eps):
    m, n = 2 * k + 1, 4 * k + 2
    delta = eps ** (1.0 / k) / (256.0 * k * k)
    rows = []
    idx = lambda c, l: c * m + l

    def add(re, pr, raw, kind, pol):
        rows.append((tuple(sorted(re)), tuple(sorted(pr)), raw, kind, pol))

    for c in range(2):
        for ell in range(m):
            add([idx(c, 0), idx(0, ell)], [idx(c, lab(1, 1)), idx(0, ell)], 1.0, "prod", 1)
            add([idx(c, 0), idx(1, ell)], [idx(c, lab(1, -1)), idx(1, ell)], 1.0, "prod", -1)
    for i in range(2, k + 1):
        for c in range(2):
            for d in range(2):
                for s in (1, -1):
                    p = idx(d, lab(i - 1, s))
                    add([idx(c, 0), p], [idx(c, lab(i, s)), p], 1.0, "prod", s)
    for i in range(1, k + 1):
        for c in range(2):
            for s in (1, -1):
                for d in range(2):
                    for ell in range(m):
                        p = idx(d, ell)
                        add([idx(c, lab(i, s)), p], [idx(c, 0), p], delta, "reset", s)
    for i in range(1, k + 1):
        for c in range(2):
            for d in range(2):
                add([idx(c, lab(i, 1)), idx(d, lab(i, -1))], [idx(c, 0), idx(d, 0)], 1.0, "cancel", 0)

    merged = {}
    for re, pr, raw, kind, pol in rows:
        key = (re, pr)
        if key in merged:
            old = merged[key]
            assert old[1:] == (kind, pol)
            merged[key] = (old[0] + raw, kind, pol)
        else:
            merged[key] = (raw, kind, pol)
    C = len(merged)
    ra = np.empty(C, int); rb = np.empty(C, int)
    raw = np.empty(C); kind = []; pol = np.empty(C, int)
    S = np.zeros((n, C))
    for j, ((re, pr), (coef, kd, po)) in enumerate(merged.items()):
        ra[j], rb[j] = re
        raw[j] = coef; kind.append(kd); pol[j] = po
        for a in re: S[a, j] -= 1.0
        for a in pr: S[a, j] += 1.0
    assert np.all(S.sum(axis=0) == 0)
    for c in range(2):
        assert np.all(S[c * m:(c + 1) * m].sum(axis=0) == 0)
    assert all(len(re) == 2 and len(pr) == 2 for re, pr in merged)
    plus = np.array([idx(c, lab(i, 1)) for c in range(2) for i in range(1, k + 1)])
    minus = np.array([idx(c, lab(i, -1)) for c in range(2) for i in range(1, k + 1)])
    return dict(k=k, eps=eps, m=m, n=n, delta=delta, ra=ra, rb=rb, raw=raw,
                kind=np.array(kind), pol=pol, S=S, plus=plus, minus=minus,
                channels=C, duplicates=len(rows) - C)


def proportions(k, sign):
    m = 2 * k + 1
    out = []
    for a in range(m):
        for b in range(m):
            pa = np.eye(m)[a]; pb = np.eye(m)[b]
            out.append((f"corner:{a}|{b}", pa, pb))
    wrong = -1 if sign > 0 else 1
    p = np.zeros(m); p[[lab(i, wrong) for i in range(1, k + 1)]] = 1.0 / k
    out.append(("all-wrong-uniform", p.copy(), p.copy()))
    p = np.zeros(m); p[1:] = 1.0 / (2 * k)
    out.append(("empty-pool-uniform", p.copy(), p.copy()))
    rng = np.random.default_rng(101300 + k)
    for j in range(N_RANDOM_STARTS):
        out.append((f"dirichlet:{j}", rng.dirichlet(np.ones(m)), rng.dirichlet(np.ones(m))))
    unique = {}
    for name, pa, pb in out:
        key = np.r_[pa, pb].round(15).tobytes()
        if key not in unique: unique[key] = (name, pa, pb)
    return list(unique.values())


def initial_batch(k, eps):
    ys, signs, names = [], [], []
    for sign in (1, -1):
        g = sign * eps; ma, mb = (1 + g) / 2, (1 - g) / 2
        for name, pa, pb in proportions(k, sign):
            ys.append(np.r_[ma * pa, mb * pb]); signs.append(sign); names.append(("+" if sign > 0 else "-") + ":" + name)
    return np.array(ys), np.array(signs), names


def c_k(k):
    return 1.0 / ((2 ** 20) * k * k * (16 ** k))


def theta_values(k, eps):
    c = c_k(k)
    return {"ck": c * eps, "10ck": 10 * c * eps, "100ck": 100 * c * eps, "0.1eps": 0.1 * eps}


def factors_adverse(model, theta, target):
    f = np.ones(model["channels"])
    for j, (kd, po) in enumerate(zip(model["kind"], model["pol"])):
        if kd == "prod": f[j] = math.exp(-theta if po == target else theta)
        elif kd == "reset": f[j] = math.exp(theta if po == target else -theta)
        else: f[j] = math.exp(-theta)
    return f


def time_bound(model, theta):
    k, eps, d = model["k"], model["eps"], model["delta"]
    q = k * math.log(4 / eps) + k * (k + 1) * math.log(16) / 2 + 0.5
    return 2 * math.exp(theta) * (1.25 + q / d)


def time_grid(T):
    a = np.linspace(0, min(10.0, T), 31)
    lo = max(1e-10, min(1e-3, T * 1e-10))
    b = np.geomspace(lo, T, 300)
    return np.unique(np.r_[a, b])


def solve_group(model, Y0, signs, names, factors, theta, horizon=2.0):
    ntr, n = len(Y0), model["n"]
    H = 2 * math.exp(theta)
    rates = model["raw"] * factors / H if factors.ndim == 1 else model["raw"][None, :] * factors / H
    ra, rb, S = model["ra"], model["rb"], model["S"]

    def rhs(t, flat):
        Y = flat.reshape(ntr, n)
        F = Y[:, ra] * Y[:, rb]
        F *= rates
        return (F @ S.T).ravel()

    T = horizon * time_bound(model, theta)
    sol = solve_ivp(rhs, (0.0, T), Y0.ravel(), method="LSODA", rtol=RTOL, atol=ATOL,
                    dense_output=True, lband=n - 1, uband=n - 1)
    if not sol.success: raise RuntimeError(sol.message)
    end_resid = np.max(np.abs(rhs(T, sol.y[:, -1])))
    if end_resid > 2e-8 and horizon < 8:
        return solve_group(model, Y0, signs, names, factors, theta, 8.0)
    ts = np.unique(np.r_[time_grid(T), sol.t])
    V = sol.sol(ts).reshape(ntr, n, -1)
    h = V[:, model["plus"], :].sum(axis=1) - V[:, model["minus"], :].sum(axis=1)
    z = signs[:, None] * h - 0.25
    good = z[:, -1] >= -1e-8
    approx = np.zeros(ntr); approx[~good] = np.inf
    brackets = {}
    for i in np.flatnonzero(good):
        bad = np.flatnonzero(z[i] < 0)
        if len(bad):
            j = bad[-1]
            if j + 1 >= len(ts):
                good[i] = False; approx[i] = np.inf
            else:
                t0, t1, z0, z1 = ts[j], ts[j + 1], z[i, j], z[i, j + 1]
                approx[i] = t0 + (t1 - t0) * (-z0) / max(z1 - z0, 1e-300)
                brackets[i] = (t0, t1)
    finite = np.flatnonzero(np.isfinite(approx))
    candidates = finite[np.argsort(approx[finite])[-min(5, len(finite)):]] if len(finite) else []
    for i in candidates:
        if i not in brackets: continue
        t0, t1 = brackets[i]
        def rootfun(t):
            y = sol.sol(t).reshape(ntr, n)[i]
            hh = y[model["plus"]].sum() - y[model["minus"]].sum()
            return signs[i] * hh - 0.25
        try: approx[i] = brentq(rootfun, t0, t1, xtol=max(1e-10, 1e-10 * t1), rtol=1e-12)
        except ValueError: pass
    ca = V[:, :model["m"], :].sum(axis=1)
    cb = V[:, model["m"]:, :].sum(axis=1)
    da = np.max(np.abs(ca - Y0[:, :model["m"]].sum(axis=1)[:, None]))
    db = np.max(np.abs(cb - Y0[:, model["m"]:].sum(axis=1)[:, None]))
    worst_i = int(np.nanargmax(approx))
    return dict(passed=int(good.sum()), total=ntr,
                worst_entry=float(approx[worst_i]), worst_name=names[worst_i],
                worst_sign=int(signs[worst_i]), min_final_signed_h=float(np.min(signs * h[:, -1])),
                mass_drift=float(np.max(np.abs(V.sum(axis=1) - 1.0))),
                color_drift=float(max(da, db)), min_concentration=float(V.min()),
                end_resid=float(end_resid), horizon=float(T))


def merge_stats(acc, cur, tag):
    if acc is None:
        acc = dict(passed=0, total=0, worst_entry=-1.0, worst_name="", worst_sign=0,
                   worst_rate="", min_final_signed_h=1e300, mass_drift=0.0,
                   color_drift=0.0, min_concentration=1e300, end_resid=0.0, horizon=0.0)
    acc["passed"] += cur["passed"]; acc["total"] += cur["total"]
    if cur["worst_entry"] > acc["worst_entry"]:
        acc["worst_entry"] = cur["worst_entry"]; acc["worst_name"] = cur["worst_name"]
        acc["worst_sign"] = cur["worst_sign"]; acc["worst_rate"] = tag
    for key in ("mass_drift", "color_drift", "end_resid", "horizon"):
        acc[key] = max(acc[key], cur[key])
    acc["min_final_signed_h"] = min(acc["min_final_signed_h"], cur["min_final_signed_h"])
    acc["min_concentration"] = min(acc["min_concentration"], cur["min_concentration"])
    return acc


def run_cell(k, ei, outpath):
    eps = EPS[ei]; model = build_model(k, eps); Y0, signs, names = initial_batch(k, eps)
    ans = dict(k=k, eps=eps, delta=model["delta"], ck=c_k(k), channels=model["channels"],
               duplicates=model["duplicates"], starts_per_sign=len(Y0) // 2, nominal=None, theta={})
    ans["nominal"] = solve_group(model, Y0, signs, names, np.ones(model["channels"]), 0.0)
    tv = theta_values(k, eps)
    for name in THETA_NAMES:
        theta = tv[name]; rand = None
        rng = np.random.default_rng(101300000 + 10000 * k + 100 * ei)
        U = rng.uniform(-1.0, 1.0, size=(N_RATE_ASSIGNMENTS, model["channels"]))
        for rid in range(N_RATE_ASSIGNMENTS):
            cur = solve_group(model, Y0, signs, names, np.exp(theta * U[rid]), theta)
            rand = merge_stats(rand, cur, f"random:{rid}")
        F = np.vstack([factors_adverse(model, theta, int(s)) for s in signs])
        adv = solve_group(model, Y0, signs, names, F, theta)
        ans["theta"][name] = dict(theta=theta, random=rand, adverse=adv)
    Path(outpath).write_text(json.dumps(ans, indent=2, sort_keys=True))


def aligned_pass(k, eps, theta):
    model = build_model(k, eps); Y0, signs, names = initial_batch(k, eps)
    F = np.vstack([factors_adverse(model, theta, int(s)) for s in signs])
    st = solve_group(model, Y0, signs, names, F, theta, horizon=8.0)
    return st["passed"] == st["total"], st


def run_edge(outpath):
    k, eps = 2, 1e-3
    lo, hi = 0.0, 0.1 * eps
    ok, st = aligned_pass(k, eps, hi)
    while ok and hi < 1.0:
        lo, hi = hi, 2 * hi; ok, st = aligned_pass(k, eps, hi)
    assert not ok
    for _ in range(24):
        mid = (lo + hi) / 2; ok, st = aligned_pass(k, eps, mid)
        if ok: lo = mid
        else: hi = mid
    oklo, slo = aligned_pass(k, eps, lo); okhi, shi = aligned_pass(k, eps, hi)
    ans = dict(k=k, eps=eps, definition="paired sign-mirrored aligned adverse assignment over the full start panel",
               theta_pass=lo, theta_fail=hi, ratio_pass=lo / eps, ratio_fail=hi / eps,
               pass_stats=slo, fail_stats=shi)
    Path(outpath).write_text(json.dumps(ans, indent=2, sort_keys=True))


def run_aggregate(indir, outpath):
    cells = [json.loads(p.read_text()) for p in sorted(Path(indir).glob("cell-*.json"))]
    edge = json.loads((Path(indir) / "edge.json").read_text())
    fits = {}
    for k in (1, 2, 3):
        cc = sorted([x for x in cells if x["k"] == k], key=lambda x: x["eps"], reverse=True)
        X = np.log([1 / x["eps"] for x in cc])
        nom = np.log([x["nominal"]["worst_entry"] for x in cc])
        rob = np.log([max(x["theta"]["ck"]["random"]["worst_entry"], x["theta"]["ck"]["adverse"]["worst_entry"]) for x in cc])
        fits[str(k)] = dict(expected=1 / k, nominal_slope=float(np.polyfit(X, nom, 1)[0]),
                            ck_slope=float(np.polyfit(X, rob, 1)[0]))
    cons = dict(max_mass_drift=0.0, max_color_drift=0.0, min_concentration=1e300, max_end_resid=0.0)
    for x in cells:
        stats = [x["nominal"]]
        for v in x["theta"].values(): stats += [v["random"], v["adverse"]]
        for s in stats:
            cons["max_mass_drift"] = max(cons["max_mass_drift"], s["mass_drift"])
            cons["max_color_drift"] = max(cons["max_color_drift"], s["color_drift"])
            cons["min_concentration"] = min(cons["min_concentration"], s["min_concentration"])
            cons["max_end_resid"] = max(cons["max_end_resid"], s["end_resid"])
    Path(outpath).write_text(json.dumps(dict(cells=cells, fits=fits, edge=edge, conservation=cons,
                                            random_starts=N_RANDOM_STARTS, rate_assignments=N_RATE_ASSIGNMENTS,
                                            rtol=RTOL, atol=ATOL), indent=2, sort_keys=True))


if __name__ == "__main__":
    if sys.argv[1] == "cell": run_cell(int(sys.argv[2]), int(sys.argv[3]), sys.argv[4])
    elif sys.argv[1] == "edge": run_edge(sys.argv[2])
    elif sys.argv[1] == "aggregate": run_aggregate(sys.argv[2], sys.argv[3])
