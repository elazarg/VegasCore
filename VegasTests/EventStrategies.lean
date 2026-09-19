/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.EventCompilation
import VegasTests.SourceSetup
import VegasTests.SourceSemantics

/-! # Full-source asynchronous strategic regression instances

These instances keep private setup inside the game and exercise heterogeneous
payloads, initial commitments, deferred guards, and conditional chance.
-/

namespace VegasTests.EventStrategies

open Vegas GameTheory GameTheory.Math.Probability SourceProgram.EventLowering

noncomputable section

/-- One deviation mixture serves both private worlds of the guessing game. -/
example (scheduler : SourceSetup.fairSetup.eventGraph.PublicScheduler)
    (chosen : Bool) (who : SourceSetup.Player)
    (replacement : SourceSetup.fairSetup.eventGraph.BehavioralPolicy who) :
    ∃ mixture : FinDist
        (SourceProgram.BehavioralPolicy who SourceSetup.fairSetup.program),
      ((SourceSetup.fairSetup.eventGame scheduler).play
        (Profile.update (sig := SourceSetup.fairSetup.eventGraph.gameSignature)
          (compileEventProfile SourceSetup.fairSetup.program
            (SourceSetup.profile chosen)) who replacement)).map
              (terminalState SourceSetup.fairSetup.program) =
        mixture.bind fun alternative =>
          SourceSetup.fairSetup.run
            (Profile.update
              (sig := SourceProgram.gameSignature SourceSetup.fairSetup.program)
              (SourceSetup.profile chosen) who alternative) := by
  simpa only [SourceProgram.Setup.eventGame, EventGraph.gameForm,
    FinDist.map_bind, FinDist.bind_map] using
    scheduled_setup_deviation_law SourceSetup.fairSetup scheduler
      (SourceSetup.profile chosen) who replacement

private def mixedSetup : SourceProgram.Setup
    (Player := SourceSemantics.Player) (L := simpleExpr) where
  context := SourceSemantics.mixedInitial.context
  namesNodup := SourceSemantics.mixedInitial.namesNodup
  initialLaw := FinDist.pure SourceSemantics.mixedInitial.state
  obligations := SourceSemantics.mixedInitial.obligations
  program := SourceSemantics.mixedInitial.program
  accounts := SourceSemantics.mixedInitial.accounts

/-- The strategic theorem does not require sample-free code, homogeneous
payloads, universally accepting guards, or commitments created during play. -/
example (scheduler : mixedSetup.eventGraph.PublicScheduler)
    (utility : SourceProgram.PublicOutcome mixedSetup.program → SourceSemantics.Player → ℝ)
    (ε : ℝ) (profile : SourceProgram.BehavioralProfile mixedSetup.program) :
    IsεNash (mixedSetup.eventGame scheduler)
        (fun outcome who => utility (SourceProgram.publicOutcome mixedSetup.program
          (terminalState mixedSetup.program outcome)) who)
        ε (compileEventProfile mixedSetup.program profile) ↔
      IsεNash mixedSetup.gameForm utility ε profile :=
  mixedSetup.eventGame_approximate_nash_iff scheduler utility ε profile

end
end VegasTests.EventStrategies
