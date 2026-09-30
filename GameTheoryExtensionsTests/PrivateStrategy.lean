/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.PrivateStrategy
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Support

/-! # Correlated private randomness survives behavioral realization

A private bit is reused across two responses. The environment echoes the first
output as the second input; the response xors that input with the private bit.
The first output is random and the second is certainly false. No private bit
is recorded as a game action by the realized behavioral policy.
-/

noncomputable section

namespace GameTheoryExtensionsTests.PrivateStrategy

open GameTheory.Protocol.PrivateStrategy GameTheory.Math.Probability

def strategy : Strategy Bool Bool Bool where
  initial := (PMF.uniformOfFintype _)
  respond memory input := PMF.pure (xor memory input, memory)

def observe (past : List Bool) : Bool := past.headD false

def advance (past : List Bool) (output : Bool) : PMF (List Bool) :=
  PMF.pure (output :: past)

theorem private_two (memory : Bool) : runPrivate strategy observe advance 2 [] [] memory =
    PMF.pure ([false, memory], [(memory, false), (false, memory)]) := by
  cases memory <;> simp [runPrivate, strategy, observe, advance]

theorem behavioral_two : runBehavioral (behavioral strategy) observe advance 2 [] [] =
    (PMF.uniformOfFintype Bool).map (fun bit =>
      ([false, bit], [(bit, false), (false, bit)])) := by
  rw [← realize strategy observe advance 2 [] []]
  change (PMF.uniformOfFintype Bool).bind _ = _
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro memory _
  exact private_two memory

end GameTheoryExtensionsTests.PrivateStrategy
