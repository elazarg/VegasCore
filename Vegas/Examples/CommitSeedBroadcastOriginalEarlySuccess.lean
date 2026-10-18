/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalClockZeroCut
import Vegas.Examples.CommitSeedBroadcastOriginalClockZeroEmission
import Vegas.Examples.CommitSeedBroadcastOriginalReceiptRetention

/-! # Resolved original clock-zero service emissions have true receipts -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- An original counted clock-zero service envelope is accepted at every
resolved endpoint. Its actual predeadline prefix is extracted from the same
initialized run that realizes the final physical history. -/
theorem original_clock_zero_emission_resolved_accepted (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (resolved : (originalCoordinate owner).Resolved execution.application)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : (0, message) ∈ (PhaseSeedScheduler.localInput runtime leaks
      (originalCoordinate owner) owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner execution := by
  classical
  by_contra unaccepted
  let players := countedMenu.uniformResponses
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have finished : 28 ≤ execution.environmentRecall.length := by
    by_contra early
    have request := original_request_of_unaccepted_before_expiry seeds _ raw owner unaccepted
      (by change execution.environmentRecall.length < 28; omega)
    exact resolved.not_request _ _ owner request
  have bounded : 26 < execution.environmentRecall.length := by omega
  let entry := execution.environmentRecall[26]
  have recorded : execution.environmentRecall = execution.environmentRecall.take 26 ++
      entry :: execution.environmentRecall.drop 27 := by
    rw [List.getElem_cons_drop bounded, List.take_append_drop]
  have supported := countedMenu.roundSupported_uniform initial horizon (family seeds) trace
  have initialized := supported.2
  rw [ReactiveApplication.roundsFrom, PMF.support_bind] at initialized
  obtain ⟨state, stateSupport, initialized⟩ := Set.mem_iUnion₂.mp initialized
  rw [initial, PMF.mem_support_pure_iff] at stateSupport
  subst state
  obtain ⟨used, rest, before, middle, _length, prior, recalled, viewed,
    chosen, dispatched, future⟩ :=
    app.runRounds_recorded_entry (family seeds) players execution.environmentRecall.length
      initialExecution execution initialized (execution.environmentRecall.take 26) entry
        (execution.environmentRecall.drop 27) (by simpa only [initialExecution,
          ReactiveApplication.Execution.initial, List.nil_append] using recorded)
  change before.environmentRecall = execution.environmentRecall.take 26 at recalled
  have count : before.environmentRecall.length = 26 := by
    rw [recalled, List.length_take, Nat.min_eq_left (Nat.le_of_lt bounded)]
  have usedEq : used = 26 := by
    have accounted := app.runRounds_environmentRecall_length (family seeds) players used
      initialExecution before prior
    change before.environmentRecall.length = 0 + used at accounted
    omega
  have sourceSupported : before ∈
      (app.roundsFrom initial (family seeds) players used).support := by
    rw [ReactiveApplication.roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨initialState, by rw [initial]; simp, prior⟩
  have within : used ≤ horizon := by
    have accounted : execution.environmentRecall.length + remaining = horizon := supported.1
    omega
  obtain ⟨beforeTrace⟩ := countedMenu.trace_roundsFrom initial horizon (family seeds) players
    (fun who past view action member =>
      (countedMenu.uniformResponses_support who past view action).mp member)
    used within before sourceSupported
  have prefixEmission := original_clock_zero_emission_before_twenty_six countedMenu seeds remaining
    execution trace owner bounded message emitted
  change (0, message) ∈ (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner)
    owner (execution.environmentRecall.take 26) entry.beforeView).emissions at prefixEmission
  rw [← recalled, viewed] at prefixEmission
  have actualEmission : (0, message) ∈ (PhaseSeedScheduler.localInput runtime leaks
      (originalCoordinate owner) owner before.environmentRecall
        (before.observeEnvironment app)).emissions := prefixEmission
  obtain ⟨declaration, member, issued, zero⟩ := original_clock_zero_emission_recorded countedMenu
    seeds (horizon - used) before beforeTrace owner message actualEmission
  have sourceRaw := countedMenu.toRawTrace initial horizon (family seeds) beforeTrace
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seeds) (horizon - used) before beforeTrace
  obtain ⟨_input, authored, tagged, named⟩ := PhaseSeedScheduler.localInput_emission_authentic
    runtime leaks before (originalCoordinate owner) owner words
      (app.history_inputRecall initial horizon (family seeds) sourceRaw) 0 message actualEmission
  have accepted := original_clock_zero_recorded_accepted seeds
    ⟨horizon - used, none, before⟩ beforeTrace
    owner declaration member message issued authored tagged named zero (by
      change before.environmentRecall.length ≤ 26
      exact count.le) (by
      rw [count]
      unfold earlyPosition
      have bound := (seeds.1.symm owner).isLt
      omega)
  have firstRound : middle ∈ (app.round (family seeds) players before).support := by
    rw [ReactiveApplication.round, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨entry.command, chosen, dispatched⟩
  have suffix : execution ∈ (app.runRounds (family seeds) players (rest + 1) before).support := by
    change execution ∈ ((app.round (family seeds) players before).bind
      (app.runRounds (family seeds) players rest)).support
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨middle, firstRound, future⟩
  exact unaccepted (original_binding_accepted_runRounds (family seeds) players (rest + 1) before
    execution suffix owner accepted)

end Vegas.Examples.CommitSeedBroadcast
