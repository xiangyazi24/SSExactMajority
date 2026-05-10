/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Time Lower Bound

Theorem 3 of Kanaya et al. (2025): any silent self-stabilizing
exact majority protocol requires Ω(n log n) expected parallel time.

The proof relies on probabilistic scheduling (uniform random pair
selection) and information-theoretic counting, which requires a
probability framework not currently in this formalization.

The state-space lower bound (Theorem 2, in Space.lean) is the
combinatorial core; the time lower bound lifts it via a coupon-
collector argument on Ω(n) distinct states.
-/

import SSExactMajority.Defs.Execution

namespace SSEM

-- Time lower bound infrastructure is not yet formalized.
-- See Space.lean for the combinatorial foundation (Theorem 2).

end SSEM
