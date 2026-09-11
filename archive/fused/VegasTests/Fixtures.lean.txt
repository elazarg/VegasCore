/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core

/-! # Shared native-runtime test fixtures -/

namespace VegasTests

open Vegas

abbrev TestPlayer := Fin 2

def fairCoin : RationalLaw Bool where
  entries := [(false, 1 / 2), (true, 1 / 2)]
  normalized := by norm_num

end VegasTests
