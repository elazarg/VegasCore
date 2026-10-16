/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceTapePolicy

/-! # Resolved own-service episodes under the complete immutable tape policy -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode


/-- Every actually remembered response of the complete policy is consistent
with its local address splice. All other event tapes and old own history remain
in the outside continuation; no per-event policy restart is made. -/
theorem phaseCountServiceTapePolicy_local_consistent
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (horizon : Nat)
    (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
    (plan : RuntimePhasePlan graph) (inputs : PMF (serviceGraph setup mode).Inputs)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (coordinate : PhaseSeedAddress graph) (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout coordinate.1.event = .binding who payload)
    (consistent : (phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
        failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who).Consistent
          (control.execution.recall who)) :
    (PhaseCount.bindingServiceTapeMember runtime leaks bounds
      (phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who) who coordinate.1 payload
      (fun past view => (values who coordinate.1.event payload binding past view).map
        PublicationResult.success)
      (choose who coordinate.1) failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      horizon (tapes coordinate)).Consistent (control.execution.recall who) := by
  classical
  let whole := phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose failure
      timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who
  let localMember := PhaseCount.bindingServiceTapeMember runtime leaks bounds
      (phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who) who coordinate.1 payload
      (fun past view => (values who coordinate.1.event payload binding past view).map
        PublicationResult.success)
      (choose who coordinate.1) failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      horizon (tapes coordinate)
  have atoms (before : List (app).PlayerEntry) (entry : (app).PlayerEntry)
      (after : List (app).PlayerEntry)
      (recalled : control.execution.recall who = before ++ entry :: after) :
      entry.action ∈ (localMember before entry.beforeView).support := by
    obtain ⟨priorControl, prior, _isPrefix, _active, pastEq, viewed, _legal⟩ :=
      (PhaseCount.onePacketMenu runtime leaks bounds).recorded_response_at
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler control trace who before
        entry after recalled
    have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler prior
    obtain ⟨input, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
        scheduler
      raw
    have budget := (phaseApplication_seedBudget runtime leaks).history _ horizon scheduler
      (fun state member => by
        obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
        exact PhaseRuntimeState.initial_seedBudget plan draw) raw
    have faithful := recalled ▸ consistent
    rw [← List.singleton_append, ← List.append_assoc] at faithful
    have offered := (whole.consistent_snoc_iff before entry).mp
      (ReactiveApplication.Policy.Consistent.of_append faithful) |>.2
    have equal := phaseCountServiceTapePolicy_local_member setup mode runtime leaks bounds values
        choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes coordinate who payload
      binding priorControl.execution valid budget
    rw [← pastEq, viewed] at offered ⊢
    change entry.action ∈ (localMember (priorControl.execution.recall who)
      (priorControl.execution.observe app who)).support
    change whole (priorControl.execution.recall who)
        (priorControl.execution.observe app who) = localMember
          (priorControl.execution.recall who) (priorControl.execution.observe app who) at equal
    rw [equal] at offered
    exact offered
  have build (past : List (app).PlayerEntry) :
      past <+: control.execution.recall who → localMember.Consistent past := by
    induction past using List.reverseRecOn with
    | nil => exact fun _ => .nil
    | append_singleton before entry ih =>
        intro isPrefix
        obtain ⟨after, recalled⟩ := isPrefix
        refine .snoc entry (ih ?_) ?_
        · exact ⟨entry :: after, by simpa only [List.append_assoc, List.singleton_append]
            using recalled⟩
        · exact atoms before entry after (by
            simpa only [List.append_assoc, List.singleton_append] using recalled.symm)
  exact build _ (List.prefix_refl _)

/-- The actual complete immutable Q prescription has the same resolved binding
success in any two genuine episodes with the same original local service seed
and tape. Other owners, domain contents and all physical interleavings may vary.
The full calendar and packet quotient are the quantified service contract. -/
theorem phaseCountServiceTapePolicy_accepted_iff_of_resolved
  (values : ∀ (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
    (serviceGraph setup mode).outputLayout event = .binding owner payload →
      List (app).PlayerEntry → (app).PlayerView → PMF (L.Val payload))
  (choose : Player → CommitAttemptEvent graph → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (horizon : Nat)
    (tapes : PhaseSeedAddress (serviceGraph setup mode) → Fin horizon → Bool × Bool)
    (plan : RuntimePhasePlan graph) (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (inputs : PMF (serviceGraph setup mode).Inputs)
    {LocalSeed RestSeed : Type}
    (seedLaw : PMF (RestSeed × (PhaseSeedAddress graph → LocalSeed)))
    (family : (RestSeed × (PhaseSeedAddress graph → LocalSeed)) → (app).Scheduler)
    (calendar : PhaseService.PrivateActivationCalendar runtime leaks bounds plan inputs horizon
      seedLaw family)
    (privateSuccess : PhaseService.PrivateBindingSuccess runtime leaks bounds plan inputs horizon
      seedLaw family)
    (firstSeeds secondSeeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (firstSupport : firstSeeds ∈ seedLaw.support) (secondSupport : secondSeeds ∈ seedLaw.support)
    (who : Player) (coordinate : PhaseSeedAddress graph) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout coordinate.1.event = .binding who payload)
    (capacity : horizon ≤ bounds.candidateCount)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (firstRemaining secondRemaining : Nat) (first second : (app).Execution)
    (firstTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon (family firstSeeds)).Trace
      (some ⟨firstRemaining, none, first⟩))
    (secondTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon (family secondSeeds)).Trace
      (some ⟨secondRemaining, none, second⟩))
    (firstReady : ∃ (before : (app).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon (family firstSeeds)).Trace
        (some before)), TracePrefix prior firstTrace ∧
          before.execution.application.SeedRequest who coordinate.1)
    (secondReady : ∃ (before : (app).Control)
      (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon (family secondSeeds)).Trace
        (some before)), TracePrefix prior secondTrace ∧
          before.execution.application.SeedRequest who coordinate.1)
    (firstResolved : coordinate.1.Resolved first.application)
    (secondResolved : coordinate.1.Resolved second.application)
    (sameSeed : firstSeeds.2 coordinate = secondSeeds.2 coordinate)
    (firstConsistent : (phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
        failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who).Consistent (first.recall
          who))
    (secondConsistent : (phaseCountServiceTapePolicy setup mode runtime leaks bounds values choose
        failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who).Consistent (second.recall
          who)) :
    PhaseService.BindingAccepted runtime leaks coordinate.1 who first ↔
      PhaseService.BindingAccepted runtime leaks coordinate.1 who second := by
  have firstLocal := phaseCountServiceTapePolicy_local_consistent setup mode runtime leaks bounds
      values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan inputs
    (family firstSeeds) ⟨firstRemaining, none, first⟩ firstTrace coordinate who payload binding
    firstConsistent
  have secondLocal := phaseCountServiceTapePolicy_local_consistent setup mode runtime leaks bounds
      values choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes plan inputs
    (family secondSeeds) ⟨secondRemaining, none, second⟩ secondTrace coordinate who payload binding
    secondConsistent
  exact PhaseCount.bindingServiceTapeMember_accepted_iff_of_resolved runtime leaks bounds plan
    ordered inputs horizon (phaseCountServiceTapePolicy setup mode runtime leaks bounds values
        choose failure timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
      slotBounded rawWeight rawNonnegative rawBounded horizon tapes who) seedLaw family calendar
    privateSuccess firstSeeds secondSeeds firstSupport secondSupport who coordinate payload
    (fun past view => (values who coordinate.1.event payload binding past view).map
      PublicationResult.success)
    (fun past view => (values who coordinate.1.event payload binding past view).map
      PublicationResult.success)
    (choose who coordinate.1) failure timing firstNonnegative firstBounded timingNonnegative
    timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
    capacity (tapes coordinate) firstRemaining secondRemaining first second firstTrace secondTrace
    binding firstReady secondReady firstResolved secondResolved sameSeed catalogue firstLocal
    secondLocal

end Vegas
