module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketHonestContinuation
public import Vegas.Game.OnePacketSwapRegular
public import Vegas.Game.OnePacketChanceSourceLaw

@[expose] public section

/-! # Native realization of every intended source position

Every legal intended source history has a legal native scheduler boundary with
the exact same decoded source state. A fully mixed reference assessment supplies
positive support for arbitrary legal source choices; the preserved equilibrium
need not reach the source position. The construction uses the actual scheduler,
the actual service contracts and the exact stopped chance and owner kernels.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "N" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler

/-- Every supported source setup draw has a legal native initial boundary. -/
theorem exists_initial_native_boundary
    (wellFormed : setup.WellFormed)
    (profile : BehavioralProfile setup.program)
    (inputs : State L setup.context) (supported : inputs ∈ setup.initialLaw.support) :
    ∃ (start : (E).History) (execution : (application setup timeouts leaks).Execution),
      start.state = some ⟨horizon - execution.environmentRecall.length, none, execution⟩ ∧
      ReachedBoundary setup timeouts leaks horizon scheduler 0 execution ∧
      sourceServicePrefix? setup 0 execution.application.config =
        some (ProtocolState.entry setup.program (Config.initial inputs)) ∧
      ProtocolState.Intended setup.program (ProtocolState.entry setup.program (Config.initial
        inputs)) := by
  let native := EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs inputs)
  let execution := ReactiveApplication.Execution.initial (application setup timeouts leaks) native
  have initial : native ∈ (initialLaw setup).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨inputs, supported, rfl⟩
  have legal : (E).Legal none (fun _ => none) := by
    refine ⟨by change ¬ False; trivial, ?_⟩
    intro who
    change ¬ ((none : Option Player) = some who)
    simp
  have reached : some ⟨horizon, none, execution⟩ ∈
      ((E).step none ⟨fun _ => none, legal⟩).support := by
    change some (⟨horizon, none, execution⟩ : (application setup timeouts leaks).Control) ∈
      ((initialLaw setup).map fun native =>
        some (⟨horizon, none, ReactiveApplication.Execution.initial
          (application setup timeouts leaks) native⟩ :
            (application setup timeouts leaks).Control)).support
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨native, initial, rfl⟩
  let start : (E).History := ⟨_, .extend .start (fun _ => none) legal reached⟩
  have state : start.state =
      some ⟨horizon - execution.environmentRecall.length, none, execution⟩ := by
    simp [start, execution, ReactiveApplication.Execution.initial]
  let residual := SourceResidual.initial setup profile inputs
  have intended : ProtocolState.Intended setup.program
      (ProtocolState.entry setup.program (Config.initial inputs)) :=
    ProtocolState.intended_entry setup.program _
      (setup.initialConfig_intended wellFormed supported)
      (wellFormed.guardsSatisfiable inputs supported)
  refine ⟨start, execution, state, ?_, residual.decode, intended⟩
  apply reachedBoundary_of_onePacket bounds start state
    (by simp [execution, ReactiveApplication.Execution.initial])
    residual.checkpoint.ordered ?_ _ residual.decode intended
  intro event beyond who entry recalled
  simp [execution, ReactiveApplication.Execution.initial] at recalled

/-- A fully mixed reference gives every legal intended source successor
positive support in the canonical source kernel at an actual owner turn. -/
theorem source_step_mem_support_honest_kernel_of_fullyMixed
    (source : setup.intendedModel.BehavioralAssessment) (full : source.IsFullyMixed)
    (history : setup.intendedProtocol.History)
    {point : ProtocolState setup.program} (current : history.state = some point)
    (joint : Player → Option (OwnAction Player L))
    (legal : setup.intendedProtocol.Legal history.state joint)
    {target : ProtocolState setup.program}
    (realized : some target ∈ (setup.intendedProtocol.step history.state ⟨joint, legal⟩).support)
    (execution : (application setup timeouts leaks).Execution) {rank : Nat}
    (ordered : execution.application.config.cut.IsPrefix rank)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (who : Player) (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (clear : execution.application.config.defaulted = ∅) :
    target ∈ (ProtocolState.behavioralStateStep setup.program
      (setup.intendedOpeningProfile source.strategy) point).support := by
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have decodedHere := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have actsHere : ProtocolView.actor who setup.program
      (ProtocolState.observe who setup.program point) = some who := by
    rw [decodedPoint_actor who ready decodedHere, owned]
    simp [clear]
  have active : setup.intendedProtocol.active history.state who := by
    rw [current]
    change ProtocolView.actor who setup.program (ProtocolState.observe who setup.program point) =
      some who
    exact actsHere
  have available : joint who ∈ setup.intendedModel.menu who
      (setup.intendedModel.infoOf who history.trace) :=
    (setup.intendedModel.menu_adequate who history.trace (joint who)).mpr (by
      cases chosen : joint who <;> simpa only [LegalOption, chosen] using legal.2 who)
  have someAction : ∃ action, joint who = some action := by
    cases chosen : joint who with
    | none => exact ((show ¬ setup.intendedProtocol.active history.state who from
        by simpa only [chosen] using legal.2 who) active).elim
    | some action => exact ⟨action, rfl⟩
  obtain ⟨action, chosen⟩ := someAction
  let site : setup.intendedModel.InformationSite who :=
    ⟨_, ⟨⟨history, rfl⟩, legal.1, action, by simpa only [chosen] using available⟩⟩
  let sourceChoice : setup.intendedModel.Choice who site.1 := ⟨joint who, available⟩
  have supportedChoice := full who site sourceChoice
  have project : projectView setup timeouts leaks who
      (some (execution.logs who, execution.observe (application setup timeouts leaks) who)) =
      setup.intendedModel.infoOf who history.trace := by
    rw [projectView_observe setup timeouts leaks who execution rank ordered point decoded,
      setup.intended_info, current]
  have asIfSupported : joint who ∈ (asIfHonestProfile setup timeouts leaks source who
      (some (execution.logs who, execution.observe (application setup timeouts leaks) who))).support
      := by
    unfold asIfHonestProfile
    rw [project]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨sourceChoice, supportedChoice, rfl⟩
  have reached : target ∈ (ProtocolState.step setup.program point joint).support := by
    change some target ∈ (setup.protocolStep history.state joint).support at realized
    rw [current] at realized
    obtain ⟨found, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
    cases Option.some.inj same
    exact supported
  rw [ProtocolState.step_eq_of_actor who who setup.program point joint actsHere] at reached
  rw [← asIfHonest_bind_step_eq_behavioralStateStep (timeouts := timeouts) source who execution
    ordered decoded intended turn (by rw [clear]; exact Finset.notMem_empty _) (execution.logs who)]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨joint who, asIfSupported, reached⟩

/-- Every legal owner successor of a realized source position has a legal
clean native successor boundary with exactly that decoded source state. -/
theorem exists_owned_successor_native_boundary
    (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : AsyncTimely timeouts delay bound)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (certificate : (E).WellFoundedHistories)
    (source : setup.intendedModel.BehavioralAssessment) (full : source.IsFullyMixed)
    (history : setup.intendedProtocol.History)
    {point : ProtocolState setup.program} (currentSource : history.state = some point)
    (joint : Player → Option (OwnAction Player L))
    (legal : setup.intendedProtocol.Legal history.state joint)
    {target : ProtocolState setup.program}
    (realized : some target ∈ (setup.intendedProtocol.step history.state ⟨joint, legal⟩).support)
    (start : (E).History) (execution : (application setup timeouts leaks).Execution) {rank : Nat}
    (current : start.state =
      some ⟨horizon - execution.environmentRecall.length, none, execution⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank execution)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (owner : Player) (event : (graph setup).EventId) (atRank : event.val = rank)
    (owned : (graph setup).actor? event = some owner) :
    ∃ (final : (E).History) (anchor : (application setup timeouts leaks).Execution),
      final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
      ReachedBoundary setup timeouts leaks horizon scheduler (rank + 1) anchor ∧
      sourceServicePrefix? setup (rank + 1) anchor.application.config = some target ∧
      ProtocolState.Intended setup.program target := by
  classical
  let players := honestProfile setup timeouts leaks bounds (initialLaw setup) horizon scheduler
    source
  let waiting := fun callback : (E).History =>
    (application setup timeouts leaks).actor callback.state = some owner
  obtain ⟨callback, supported⟩ := ((N).runBehavioralUntil certificate players waiting
    start).support_nonempty
  have clear := defaulted_eq_empty_of_decodedIntended
    ((decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded) intended
  obtain ⟨remaining, anchor, callbackState, same, callbackClear, _recalled, pending, never⟩ :=
    counted_boundary_firstActivation (timeouts := timeouts) opportunity timely completes
      certificate players start current boundary clear decoded intended owner event atRank owned
      callback supported
  have turn := (pendingEvent_spec (timeouts := timeouts) pending).1
  have sourceSupport := source_step_mem_support_honest_kernel_of_fullyMixed source full history
    currentSource joint legal realized anchor (same ▸ boundary.ordered) (same ▸ decoded) intended
    owner event turn callbackClear
  have installed : Profile.update (sig := (N).behavioralSignature) players owner
      ((players owner).withLaw ((N).infoOf owner callback.trace)
        (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          source owner ((N).infoOf owner callback.trace))) = players := by
    change Profile.update (sig := (N).behavioralSignature) players owner
      ((players owner).withLaw ((N).infoOf owner callback.trace)
        (players owner ((N).infoOf owner callback.trace))) = players
    rw [BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self]
  have sourceLaw := counted_firstActivation_honest_sourceLaw (timeouts := timeouts) opportunity
    inclusion timely completes covers capacity source certificate players callback callbackState
      callbackClear event pending never (same ▸ boundary.ordered) (same ▸ decoded) intended _ rfl
  rw [installed] at sourceLaw
  have projectedSupport : some target ∈
      (((N).runBehavioralUntil certificate players
        (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
          ¬ ReactiveApplication.stateInvariant (app := application setup timeouts leaks)
            (fun native : EventGraphRuntime.State (graph setup) => native.config.defaulted = ∅)
            stop.state) callback).map
        (fun stop => nativeDecodedState setup timeouts leaks stop.state)).support := by
    rw [sourceLaw]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨target, sourceSupport, rfl⟩
  obtain ⟨final, finalSupport, decodedFinal⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp projectedSupport
  have intendedTarget : ProtocolState.Intended setup.program target :=
    intended_of_history wellFormed (.extend history.trace joint legal realized) target rfl
  have ready := (anchor.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ owner event turn).1
  obtain ⟨next, nextState, _nextClear, _completed, nextDecoded, nextBoundary⟩ :=
    counted_stopped_boundary_of_intended (timeouts := timeouts) completes certificate players
      callback callbackState (same ▸ boundary.ordered) event ready final finalSupport
      decodedFinal intendedTarget
  exact ⟨final, next, nextState, nextBoundary, nextDecoded, intendedTarget⟩

/-- Every source chance successor of a realized source position has a legal
clean native successor boundary with exactly that decoded source state. -/
theorem exists_chance_successor_native_boundary
    (wellFormed : setup.WellFormed)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories)
    (source : setup.intendedModel.BehavioralAssessment)
    (history : setup.intendedProtocol.History)
    {point : ProtocolState setup.program} (currentSource : history.state = some point)
    (joint : Player → Option (OwnAction Player L))
    (legal : setup.intendedProtocol.Legal history.state joint)
    {target : ProtocolState setup.program}
    (realized : some target ∈ (setup.intendedProtocol.step history.state ⟨joint, legal⟩).support)
    (start : (E).History) (execution : (application setup timeouts leaks).Execution) {rank : Nat}
    (current : start.state =
      some ⟨horizon - execution.environmentRecall.length, none, execution⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank execution)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (focal : Player) (event : (graph setup).EventId) (atRank : event.val = rank)
    (actorless : (graph setup).actor? event = none) :
    ∃ (final : (E).History) (anchor : (application setup timeouts leaks).Execution),
      final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
      ReachedBoundary setup timeouts leaks horizon scheduler (rank + 1) anchor ∧
      sourceServicePrefix? setup (rank + 1) anchor.application.config = some target ∧
      ProtocolState.Intended setup.program target := by
  let profile := setup.intendedOpeningProfile source.strategy
  let players := honestProfile setup timeouts leaks bounds (initialLaw setup) horizon scheduler
    source
  obtain ⟨found, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts) profile
    (bounds.onePacketMenu timeouts leaks) horizon scheduler start.trace _ current
  have sameRank := residual.checkpoint.ordered.unique boundary.ordered
  subst found
  have ready := (ready_iff_rank setup _ rank boundary.ordered event).mpr atRank
  have noActor : ProtocolView.actor focal setup.program
      (ProtocolState.observe focal setup.program point) = none := by
    rw [decodedPoint_actor focal ready
      ((decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded), actorless]
    rfl
  have sourceSupport : target ∈ (ProtocolState.behavioralStateStep setup.program profile
      point).support := by
    rw [ProtocolState.behavioralStateStep_of_actor_none setup.program profile point focal noActor]
    change some target ∈ (setup.protocolStep history.state joint).support at realized
    rw [currentSource] at realized
    obtain ⟨found, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
    cases Option.some.inj same
    rw [ProtocolState.step_eq_of_actor_none focal setup.program point joint noActor] at supported
    exact supported
  have sourceLaw := counted_chance_stopped_sourceLaw (timeouts := timeouts) completes certificate
    players start current event atRank actorless profile residual decoded intended
  have projectedSupport : some target ∈
      (((N).runBehavioralUntil certificate players
        (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
          ¬ ReactiveApplication.stateInvariant (app := application setup timeouts leaks)
            (fun native : EventGraphRuntime.State (graph setup) => native.config.defaulted = ∅)
            stop.state) start).map
        (fun stop => nativeDecodedState setup timeouts leaks stop.state)).support := by
    rw [sourceLaw]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨target, sourceSupport, rfl⟩
  obtain ⟨final, finalSupport, decodedFinal⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp projectedSupport
  have intendedTarget : ProtocolState.Intended setup.program target :=
    intended_of_history wellFormed (.extend history.trace joint legal realized) target rfl
  obtain ⟨next, nextState, _nextClear, _completed, nextDecoded, nextBoundary⟩ :=
    counted_stopped_boundary_of_intended (timeouts := timeouts) completes certificate players
      start current boundary.ordered event ready final finalSupport decodedFinal intendedTarget
  exact ⟨final, next, nextState, nextBoundary, nextDecoded, intendedTarget⟩

omit [Fintype Player] in
/-- A nonterminal decoded source position has a ready native instruction. -/
theorem native_prefix_rank_lt_of_source_nonterminal
    {rank : Nat} (execution : (application setup timeouts leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (running : ¬ ProtocolState.terminal setup.program point) :
    rank < (graph setup).order.eventCount := by
  by_contra outside
  have within : rank ≤ (graph setup).order.eventCount := ordered.1
  have full : rank = (graph setup).order.eventCount := by omega
  subst rank
  obtain ⟨final, read, stopped⟩ := serviceSourcePrefix?_terminal setup .sequential
    execution.application.config ordered.terminal
  change sourceServicePrefix? setup (graph setup).order.eventCount
    execution.application.config = some final at read
  rw [decoded] at read
  cases Option.some.inj read
  exact running stopped

/-- Every legal intended history is represented by a legal clean native
scheduler boundary, including histories outside a later equilibrium's support. -/
theorem exists_native_boundary_of_intended_history
    (wellFormed : setup.WellFormed)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : AsyncTimely timeouts delay bound)
    (completes : ∀ control : (application setup timeouts leaks).Control,
      (E).Trace (some control) → control.execution.application.config.defaulted = ∅ →
      (application setup timeouts leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (certificate : (E).WellFoundedHistories)
    (source : setup.intendedModel.BehavioralAssessment) (full : source.IsFullyMixed)
    (focal : Player) :
    ∀ {state} (_trace : setup.intendedProtocol.Trace state),
      ∀ point, state = some point →
      ∃ (rank : Nat) (start : (E).History)
        (execution : (application setup timeouts leaks).Execution),
        start.state = some ⟨horizon - execution.environmentRecall.length, none, execution⟩ ∧
        ReachedBoundary setup timeouts leaks horizon scheduler rank execution ∧
        sourceServicePrefix? setup rank execution.application.config = some point ∧
        ProtocolState.Intended setup.program point := by
  intro state trace
  induction trace with
  | start =>
    intro point current
    cases current
  | @extend before after prior joint legal realized ih =>
    intro point currentSource
    cases before with
    | none =>
      change after ∈ (setup.initialLaw.map fun inputs =>
        some (ProtocolState.entry setup.program (Config.initial inputs))).support at realized
      obtain ⟨inputs, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
      cases Option.some.inj (same.trans currentSource)
      obtain ⟨start, execution, current, boundary, decoded, intended⟩ :=
        exists_initial_native_boundary (timeouts := timeouts) (leaks := leaks) (bounds := bounds)
          (horizon := horizon) (scheduler := scheduler) wellFormed
          (setup.intendedOpeningProfile source.strategy) inputs supported
      exact ⟨0, start, execution, current, boundary, decoded, intended⟩
    | some before =>
      let history : setup.intendedProtocol.History := ⟨some before, prior⟩
      have realizedHere : some point ∈
          (setup.intendedProtocol.step history.state ⟨joint, legal⟩).support := by
        rw [← currentSource]
        exact realized
      obtain ⟨rank, start, execution, current, boundary, decoded, intended⟩ := ih before rfl
      have running : ¬ ProtocolState.terminal setup.program before := legal.1
      have inside := native_prefix_rank_lt_of_source_nonterminal execution boundary.ordered
        decoded running
      let event : (graph setup).EventId := ⟨rank, inside⟩
      cases owned : (graph setup).actor? event with
      | none =>
        obtain ⟨final, anchor, nextState, nextBoundary, nextDecoded, nextIntended⟩ :=
          exists_chance_successor_native_boundary wellFormed completes certificate source history
            rfl joint legal realizedHere start execution current boundary decoded intended focal
              event rfl owned
        exact ⟨rank + 1, final, anchor, nextState, nextBoundary, nextDecoded, nextIntended⟩
      | some owner =>
        obtain ⟨final, anchor, nextState, nextBoundary, nextDecoded, nextIntended⟩ :=
          exists_owned_successor_native_boundary wellFormed opportunity inclusion timely completes
            covers capacity certificate source full history rfl joint legal realizedHere start
              execution current boundary decoded intended owner event rfl owned
        exact ⟨rank + 1, final, anchor, nextState, nextBoundary, nextDecoded, nextIntended⟩

end Vegas
