/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperPublicPackets
import Vegas.Examples.CommitSeedBroadcastCountedInformation
import Vegas.Examples.CommitSeedBroadcastCountedSeedTrace

/-! # The original public packet word in every compatible native history -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- A remembered receipted original clock-two view determines the exact
initial public packet word throughout the ENTIRE raw information fiber.
Neither positive equilibrium reach nor clean foreign play is assumed. -/
theorem raw_remembered_receipt_public_word_fiber
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (earlier : List app.PlayerEntry) (entry : app.PlayerEntry) (later : List app.PlayerEntry)
    (recorded : execution.recall owner = earlier ++ entry :: later)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.2.native.clock = 2)
    (receipted : entry.beforeView.receipts ≠ [])
    (target : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace)) :
    (target.1.state.map fun control => initialPublicPackets control.execution).getD ∅ =
      initialPublicPackets execution := by
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  obtain ⟨sourceSeed, ⟨sourceFixed⟩⟩ := menu_trace_fixed_seed countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) _ sourceTrace
  have sourcePackets := remembered_receipted_firstLate_packets countedMenu sourceSeed _
    sourceFixed owner earlier entry later recorded original clock receipted
  obtain ⟨count, next, state, ⟨countedTrace⟩, recalled, _observed⟩ :=
    counted_information_raw_fiber_control source remaining execution owner current target
  obtain ⟨targetSeed, ⟨targetFixed⟩⟩ := menu_trace_fixed_seed countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) _ countedTrace
  have targetPackets := remembered_receipted_firstLate_packets countedMenu targetSeed _ targetFixed
    owner earlier entry later (recalled.trans recorded) original clock receipted
  rw [state, Option.map_some, Option.getD_some]
  exact targetPackets.trans sourcePackets.symm

/-- Every assessment at this full information value assigns mass one to
the SAME original public packet word. This is an observable-fiber theorem;
it does not assert that earlier foreign timing trembles disappear. -/
theorem assessed_remembered_receipt_public_word
    (assessment : rawModel.BehavioralAssessment)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (earlier : List app.PlayerEntry) (entry : app.PlayerEntry) (later : List app.PlayerEntry)
    (recorded : execution.recall owner = earlier ++ entry :: later)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.2.native.clock = 2)
    (receipted : entry.beforeView.receipts ≠ [])
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace) :
    (assessment.belief owner site).map (fun history =>
      (history.1.state.map fun control => initialPublicPackets control.execution).getD ∅) =
        PMF.pure (initialPublicPackets execution) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro packets reached
  obtain ⟨target, _supported, equal⟩ := PMF.support_map .. ▸ reached
  let sameInput : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace) :=
    ⟨target.1, target.2.trans atSite⟩
  exact equal.symm.trans (raw_remembered_receipt_public_word_fiber source remaining execution
    owner current earlier entry later recorded original clock receipted sameInput)

end Vegas.Examples.CommitSeedBroadcast
