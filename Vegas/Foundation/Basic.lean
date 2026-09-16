/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.Context
import Vegas.Foundation.ExprInterface
import Vegas.Foundation.Visibility
import Vegas.Foundation.Env
import Vegas.Foundation.Payoff

/-!
# Shared Vegas base interface (umbrella)

This module re-exports the shared typed contexts, expression interface, and
visibility infrastructure. The content lives in focused modules:

* `Vegas.Foundation.Context` — plain typed contexts, `HasVar`, plain `Env`.
* `Vegas.Foundation.ExprInterface` — the embedded language interface `IExpr`.
* `Vegas.Foundation.Visibility` — `Visibility`, `BindTy`, `VCtx`, `VHasVar`, `VEnv`.
* `Vegas.Foundation.Env` — views, public projection, erasure, sampling.
* `Vegas.Foundation.Payoff` — outcomes and payoff/guard evaluation.

The source language, graph IR, and surface prototype share these definitions.
-/
