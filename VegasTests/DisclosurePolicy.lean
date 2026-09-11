/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.OptionalDisclosure

/-! # Finite strategies for the disclosure source fixture -/

noncomputable section

namespace VegasTests.OptionalDisclosure

open GameTheory.Math.Probability

structure SenderStrategy where
  binding : FinDist Bool
  complete : Bool → Bool → FinDist Bool

abbrev ResponderStrategy := Bool → Option Bool → FinDist Bool

end VegasTests.OptionalDisclosure
