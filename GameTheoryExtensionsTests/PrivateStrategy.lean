/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.PrivateStrategy

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
  initial := PMF.uniformOfFintype
  respond memory input := PMF.pure (xor memory input, memory)

def observe (past : List Bool) : Bool := past.headD false

def advance (past : List Bool) (output : Bool) : PMF (List Bool) :=
  PMF.pure (output :: past)

theorem private_two (memory : Bool) : runPrivate strategy observe advance 2 [] [] memory =
    PMF.pure ([false, memory], [(memory, false), (false, memory)]) := by
  cases memory <;> simp [runPrivate, strategy, observe, advance]

theorem behavioral_two : runBehavioral (behavioral strategy) observe advance 2 [] [] =
    (PMF.uniformOfFintype (α := Bool)).map (fun bit =>
      ([false, bit], [(bit, false), (false, bit)])) := by
  rw [← realize strategy observe advance 2 [] []]
  change (PMF.uniformOfFintype (α := Bool)).bind _ = _
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro memory _
  exact private_two memory

end GameTheoryExtensionsTests.PrivateStrategy
