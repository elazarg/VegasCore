/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastEarlyLedger
import Vegas.Examples.CommitSeedBroadcastTailRecall
import Interaction.ReactiveRecordedResponse

/-! # The remembered bad-clock-two ledger fixes the original public packet word -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

open Classical in
/-- The original public envelope set, read from the immutable native snapshot. -/
def initialPublicPackets (execution : app.Execution) : Finset (Message Player app.Payload) :=
  ((execution.environmentRecall[3]?).map fun snapshot =>
    snapshot.beforeView.network.inputs.toFinset).getD ∅

open Classical in
/-- A recalled first-late view with a physical receipt is necessarily after
the middle block. Its ledger is the original packet set, permanently retained
in the owner's full information even after a later retry or phase retirement. -/
theorem remembered_receipted_firstLate_packets (menu : app.ResponseMenu)
    (seed : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seed)).Trace (some current))
    (owner : Player) (earlier : List app.PlayerEntry) (entry : app.PlayerEntry)
    (later : List app.PlayerEntry)
    (recorded : current.execution.recall owner = earlier ++ entry :: later)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.2.native.clock = 2)
    (receipted : entry.beforeView.receipts ≠ []) :
    initialPublicPackets current.execution = entry.beforeView.messages.ledger.toFinset := by
  classical
  obtain ⟨before, beforeTrace, retained, active, _past, viewed, _allowed⟩ :=
    menu.recorded_response_at initial horizon (family seed) current trace owner earlier entry later
      recorded
  let rawBefore := menu.toRawTrace initial horizon (family seed) beforeTrace
  have originalBefore : before.execution.application.attempt = originalAttempt :=
    (congrArg (fun view : app.PlayerView => view.application.2.attempt) viewed).symm.trans original
  have clockBefore : before.execution.application.current.native.clock = 2 :=
    (congrArg (fun view : app.PlayerView => view.application.2.native.clock)
      viewed).symm.trans clock
  have bad : seed.2 owner = false := by
    cases bit : seed.2 owner with
    | false => rfl
    | true =>
        have empty := original_good_firstLate_receipts_empty seed before rawBefore owner active
          originalBefore clockBefore bit
        have observed := congrArg ReactiveApplication.PlayerView.receipts viewed
        exact (receipted (observed.trans empty)).elim
  have lower : 12 ≤ before.execution.environmentRecall.length :=
    (original_first_late_bad_iff seed before rawBefore owner active originalBefore clockBefore).mp
      bad
  let sourceSnapshot := before.execution.environmentRecall[3]'(by omega)
  have sourceSelected : before.execution.environmentRecall[3]? = some sourceSnapshot :=
    List.getElem?_eq_getElem (by omega)
  have prefixEnv := environment_prefix menu seed before current beforeTrace trace retained
  obtain ⟨rest, extended⟩ := prefixEnv
  have retainedSnapshot : current.execution.environmentRecall[3]? = some sourceSnapshot := by
    rw [← extended, List.getElem?_append_left (by omega)]
    exact sourceSelected
  have ledger := bad_firstLate_ledger_packets seed before rawBefore owner active originalBefore
    clockBefore bad sourceSnapshot sourceSelected
  have observedLedger := congrArg
    (fun view : app.PlayerView => view.messages.ledger.toFinset) viewed
  change entry.beforeView.messages.ledger.toFinset =
    before.execution.network.ledger.toFinset at observedLedger
  unfold initialPublicPackets
  rw [retainedSnapshot, Option.map_some, Option.getD_some]
  exact (observedLedger.trans ledger).symm

open Classical in
/-- Equal whole own recall cannot mix different initial public packet words
at a later helper input: its remembered receipted clock-two view already fixes P. -/
theorem same_helper_recall_initial_packets (menu : app.ResponseMenu)
    (leftSeed rightSeed : Seeds) (left right : app.Control)
    (leftTrace : (menu.protocol initial horizon (family leftSeed)).Trace (some left))
    (rightTrace : (menu.protocol initial horizon (family rightSeed)).Trace (some right))
    (owner : Player) (earlier : List app.PlayerEntry) (entry : app.PlayerEntry)
    (later : List app.PlayerEntry)
    (recorded : left.execution.recall owner = earlier ++ entry :: later)
    (same : left.execution.recall owner = right.execution.recall owner)
    (original : entry.beforeView.application.2.attempt = originalAttempt)
    (clock : entry.beforeView.application.2.native.clock = 2)
    (receipted : entry.beforeView.receipts ≠ []) :
    initialPublicPackets left.execution = initialPublicPackets right.execution := by
  classical
  have leftWord := remembered_receipted_firstLate_packets menu leftSeed left leftTrace owner
    earlier entry later recorded original clock receipted
  have rightWord := remembered_receipted_firstLate_packets menu rightSeed right rightTrace owner
    earlier entry later (same.symm.trans recorded) original clock receipted
  exact leftWord.trans rightWord.symm

end Vegas.Examples.CommitSeedBroadcast
