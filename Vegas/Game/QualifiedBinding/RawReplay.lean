/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.QualifiedBinding.SourceImage

/-! # Actual raw execution and sequential callback kernels -/

noncomputable section

namespace Vegas.PhaseProposalQualifiedBinding

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (values : ∀ who (key : setup.ProposalRecoveryComponent who),
    PMF (setup.CommitRecoveryValueChoice who key.1))

open scoped ENNReal

attribute [local implicit_reducible] InformationModel.InformationSite

variable (implementation : ReservedConcurrentImplementation setup)

local notation "nativeApplication" => implementation.application
local notation "nativeMenu" => PhaseCount.onePacketMenu implementation.runtime
  implementation.leaks implementation.bounds
local notation "nativeInitial" => implementation.initial
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  nativeMenu nativeInitial implementation.horizon implementation.scheduler


omit [Fintype Player] in
/-- Snapshot-dependent assignments retain the authentic packet emitted by a
swapped submission. Saved and retired snapshots do not enter emission. -/
private theorem sourceSnapshotAssignment_emit
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (owner : Player)
    (known : List (Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))))
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (fixed : material.evidence.FixedBy (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before.current.native)
      (sourceHandlePairs setup implementation target reference lost))) :
    (sourceSnapshotAssignment setup implementation target reference lost before).emit
        owner known (material.swap (HiddenSwap.ofPairs
          (sourceSnapshotPairs setup implementation target reference lost before.current.native)
          (sourceHandlePairs setup implementation target reference lost))) =
      before.emit owner known material := by
  unfold PhaseRuntimeState.emit
  change (⟨before.attempt,
    if before.allows _ then _ else _⟩ : CommitAttemptPacket _) = _
  have current : (sourceSnapshotAssignment setup implementation target reference lost
      before).current = before.current.swap (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost before.current.native)
        (sourceHandlePairs setup implementation target reference lost)) := rfl
  rw [current, RecoveryState.emit_swap _ before.current owner _ material fixed]

omit [Fintype Player] in
/-- The assigned application uses one snapshot-specific swap for submission
and emission. Its post-submission swap has the same field pairs. -/
private theorem sourceSnapshotAssignment_submit_emit
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (before : PhaseRuntimeState (serviceGraph setup .concurrent))
    (owner : Player)
    (known : List (Message Player (CommitAttemptPacket (serviceGraph setup .concurrent))))
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (fixed : material.evidence.FixedBy (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before.current.native)
      (sourceHandlePairs setup implementation target reference lost))) :
    let swap := HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost before.current.native)
      (sourceHandlePairs setup implementation target reference lost)
    ((sourceSnapshotAssignment setup implementation target reference lost before).submit
        owner (material.swap swap)).emit owner known (material.swap swap) =
      (before.submit owner material).emit owner known material := by
  dsimp only
  rw [sourceSnapshotAssignment_submit]
  have pairs : sourceSnapshotPairs setup implementation target reference lost
      (before.submit owner material).current.native =
        sourceSnapshotPairs setup implementation target reference lost before.current.native := by
    unfold sourceSnapshotPairs
    congr 1
    exact sourceSnapshotPair_submit setup implementation target reference lost
      before.current.native owner material
  have emitted := sourceSnapshotAssignment_emit setup implementation target reference lost
    (before.submit owner material) owner known material (by simpa only [pairs] using fixed)
  simpa only [pairs] using emitted

omit [Fintype Player] in
/-- Submission executes the assigned preparation and the identical authentic
packet. The actual response, including its alias, remains in private recall. -/
private theorem sourceReplayExecution_respond
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (original : (nativeApplication).Execution) (owner : Player)
    (response : (nativeApplication).Action)
    (fixed : ∀ material, response.transmission = some material →
      material.evidence.FixedBy (HiddenSwap.ofPairs
        (sourceSnapshotPairs setup implementation target reference lost
          original.application.current.native)
        (sourceHandlePairs setup implementation target reference lost))) :
    let swap := HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost
        original.application.current.native)
      (sourceHandlePairs setup implementation target reference lost)
    let actual := sourceReplayExecution setup implementation target reference lost recalls original
    actual.respond nativeApplication owner (swap.phaseAction response) =
      sourceReplayExecution setup implementation target reference lost
        (actual.respond nativeApplication owner (swap.phaseAction response)).recall
        (original.respond nativeApplication owner response) := by
  dsimp only
  cases response with
  | mk transmission =>
      cases transmission with
      | none => rfl
      | some material =>
          have packet := sourceSnapshotAssignment_submit_emit setup implementation target
            reference lost original.application owner (original.network.known owner) material
              (fixed material rfl)
          have submitted := sourceSnapshotAssignment_submit setup implementation target reference
            lost original.application owner material
          dsimp only at packet submitted
          change (nativeApplication).packet
              ((nativeApplication).submit
                (sourceSnapshotAssignment setup implementation target reference lost
                  original.application) owner (material.swap _))
              owner (original.network.known owner) (material.swap _) =
            (nativeApplication).packet
              ((nativeApplication).submit original.application owner material) owner
              (original.network.known owner) material at packet
          change (nativeApplication).submit
              (sourceSnapshotAssignment setup implementation target reference lost
                original.application) owner (material.swap _) =
            sourceSnapshotAssignment setup implementation target reference lost
              ((nativeApplication).submit original.application owner material) at submitted
          dsimp only [sourceReplayExecution, HiddenSwap.phaseAction, Option.map_some,
            ReactiveApplication.Execution.respond]
          rw [packet, submitted]

omit [Fintype Player] in
/-- A focal response retains its exact raw syntax. Equality of its full
actual input supplies emission equality even for ineffective evidence requests. -/
private theorem sourceReplayExecution_focal_respond
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (original : (nativeApplication).Execution) (who : Player)
    (originalCounts : PhaseCount.CountRecall implementation.runtime implementation.leaks original)
    (actualCounts : PhaseCount.CountRecall implementation.runtime implementation.leaks
      (sourceReplayExecution setup implementation target reference lost recalls original))
    (past : recalls who = original.recall who)
    (view : (sourceReplayExecution setup implementation target reference lost recalls
      original).observe nativeApplication who = original.observe nativeApplication who)
    (action : (nativeApplication).Action)
    (fixed : (HiddenSwap.ofPairs
      (sourceSnapshotPairs setup implementation target reference lost
        original.application.current.native)
      (sourceHandlePairs setup implementation target reference lost)).phaseAction action = action) :
    let actual := sourceReplayExecution setup implementation target reference lost recalls original
    actual.respond nativeApplication who action =
        sourceReplayExecution setup implementation target reference lost
          (actual.respond nativeApplication who action).recall
          (original.respond nativeApplication who action) ∧
      (actual.respond nativeApplication who action).recall who =
        (original.respond nativeApplication who action).recall who := by
  dsimp only
  cases action with
  | mk transmission =>
      cases transmission with
      | none =>
          constructor
          · rfl
          · simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
            change recalls who ++ [⟨
                (sourceReplayExecution setup implementation target reference lost recalls
                  original).observe nativeApplication who, ⟨none⟩, none⟩] =
              original.recall who ++ [⟨original.observe nativeApplication who, ⟨none⟩, none⟩]
            rw [past, view]
      | some material =>
          have materialFixed : material.swap (HiddenSwap.ofPairs
              (sourceSnapshotPairs setup implementation target reference lost
                original.application.current.native)
              (sourceHandlePairs setup implementation target reference lost)) = material := by
            exact Option.some.inj (congrArg ReactiveApplication.Action.transmission fixed)
          have submitted := sourceSnapshotAssignment_submit setup implementation target reference
            lost original.application who material
          dsimp only at submitted
          rw [materialFixed] at submitted
          change (nativeApplication).submit
              (sourceSnapshotAssignment setup implementation target reference lost
                original.application) who material =
            sourceSnapshotAssignment setup implementation target reference lost
              ((nativeApplication).submit original.application who material) at submitted
          have packet : (nativeApplication).packet
              ((nativeApplication).submit
                (sourceSnapshotAssignment setup implementation target reference lost
                  original.application) who material) who (original.network.known who) material =
              (nativeApplication).packet
                ((nativeApplication).submit original.application who material) who
                (original.network.known who) material := by
            have localEq : PhaseCount.localEnvelope implementation.runtime implementation.leaks
                who ((sourceReplayExecution setup implementation target reference lost recalls
                  original).recall who)
                ((sourceReplayExecution setup implementation target reference lost recalls
                  original).observe nativeApplication who) material =
              PhaseCount.localEnvelope implementation.runtime implementation.leaks who
                (original.recall who) (original.observe nativeApplication who) material := by
              change PhaseCount.localEnvelope implementation.runtime implementation.leaks who
                (recalls who) _ material = _
              rw [past, view]
            rw [PhaseCount.localEnvelope_eq_of_recall implementation.runtime implementation.leaks
                _ actualCounts.1 actualCounts.2.1 who material,
              PhaseCount.localEnvelope_eq_of_recall implementation.runtime implementation.leaks
                _ originalCounts.1 originalCounts.2.1 who material] at localEq
            exact congrArg Message.payload localEq
          constructor
          · dsimp only [ReactiveApplication.Execution.respond, sourceReplayExecution]
            rw [packet, submitted]
          · simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
            change recalls who ++ [⟨_, _,
                some (original.network.submit who
                  ((nativeApplication).packet
                    ((nativeApplication).submit
                      (sourceSnapshotAssignment setup implementation target reference lost
                        original.application) who material) who (original.network.known who)
                    material)).1⟩] =
              original.recall who ++ [⟨original.observe nativeApplication who, _,
                some (original.network.submit who
                  ((nativeApplication).packet
                    ((nativeApplication).submit original.application who material) who
                    (original.network.known who) material)).1⟩]
            rw [past, view, packet]

omit [Fintype Player] in
/-- A proper first registration executes the exact value selected by the
target row or by its historical lost-draw slot. No guard outcome is assumed. -/
private theorem sourceReplayExecution_proper_respond
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (original : (nativeApplication).Execution)
    (owner : Player) (event : (serviceGraph setup .concurrent).EventId)
    (payload : L.Ty) (serial : Nat) (old next : L.Val payload)
    (registered : reference.execution.application.current.native.candidates.lookup
      (owner, .prepared serial) = .openable (⟨payload, old⟩ : Raw L))
    (selected : (sourceHandleMeaning setup implementation target reference
        (owner, .prepared serial)).orElse (fun _ => lost (owner, .prepared serial)) =
      some (⟨payload, next⟩ : Raw L)) :
    let actual := sourceReplayExecution setup implementation target reference lost recalls original
    let first := phaseBindingResponse implementation.runtime implementation.leaks owner event
      payload (.success old) serial
    let second := phaseBindingResponse implementation.runtime implementation.leaks owner event
      payload (.success next) serial
    actual.respond nativeApplication owner second =
      sourceReplayExecution setup implementation target reference lost
        (actual.respond nativeApplication owner second).recall
        (original.respond nativeApplication owner first) := by
  classical
  dsimp only
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost
      original.application.current.native)
    (sourceHandlePairs setup implementation target reference lost)
  have pair : sourceHandlePairs setup implementation target reference lost
      (owner, .prepared serial) =
        some ((⟨payload, old⟩ : Raw L), (⟨payload, next⟩ : Raw L)) := by
    simp only [sourceHandlePairs, registered, selected, Option.map_some]
  have action : swap.phaseAction
      (phaseBindingResponse implementation.runtime implementation.leaks owner event payload
        (.success old) serial) =
      phaseBindingResponse implementation.runtime implementation.leaks owner event payload
        (.success next) serial := by
    simp only [swap, HiddenSwap.phaseAction, phaseBindingResponse, WitnessedSubmission.swap,
      Submission.swap, Option.map_some, HiddenSwap.ofPairs, pair, EventGraph.pairSwap,
      Equiv.swap_apply_left]
  have response := sourceReplayExecution_respond setup implementation target reference lost recalls
    original owner
      (phaseBindingResponse implementation.runtime implementation.leaks owner event payload
        (.success old) serial) (by
        intro material transmitted
        cases Option.some.inj transmitted
        trivial)
  dsimp only at response
  rw [action] at response
  exact response

omit [Fintype Player] in
/-- Including an original packet preserves its literal network and receipt
when the assigned application handles that same packet by the assigned rule. -/
private theorem sourceReplayExecution_includePending
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (original : (nativeApplication).Execution)
    (handling : ∀ id message, original.network.lookup id = some message →
      (nativeApplication).handle
          (sourceSnapshotAssignment setup implementation target reference lost
            original.application) message =
        ((nativeApplication).handle original.application message).map
          (sourceSnapshotAssignment setup implementation target reference lost))
    (id : MessageId Player) :
    (sourceReplayExecution setup implementation target reference lost recalls
        original).includePending nativeApplication id =
      sourceReplayExecution setup implementation target reference lost recalls
        (original.includePending nativeApplication id) := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases found : original.network.lookup id with
  | none =>
      dsimp only [sourceReplayExecution]
      rw [found]
  | some message =>
      dsimp only [sourceReplayExecution]
      rw [found]
      dsimp only
      rw [handling id message found]
      cases handled : (nativeApplication).handle original.application message <;> rfl

omit [Fintype Player] in
/-- Every environment branch has the exact assigned application and the
original physical observations. This derives the replay transition support
from the original branch, including its public Nature probability. -/
private theorem sourceReplayExecution_environment
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (original : (nativeApplication).Execution)
    (handling : ∀ id message, original.network.lookup id = some message →
      (nativeApplication).handle
          (sourceSnapshotAssignment setup implementation target reference lost
            original.application) message =
        ((nativeApplication).handle original.application message).map
          (sourceSnapshotAssignment setup implementation target reference lost))
    (command : (nativeApplication).Command) :
    (sourceReplayExecution setup implementation target reference lost recalls
        original).environmentStep nativeApplication command =
      (original.environmentStep nativeApplication command).map
        (sourceReplayExecution setup implementation target reference lost recalls) := by
  have observed :
      (sourceReplayExecution setup implementation target reference lost recalls
        original).observeEnvironment nativeApplication =
        original.observeEnvironment nativeApplication := by
    change
      (⟨original.network.publicView,
        (sourceSnapshotAssignment setup implementation target reference lost
          original.application).publicView, original.receipts⟩ :
          (nativeApplication).EnvironmentView) =
        ⟨original.network.publicView, original.application.publicView, original.receipts⟩
    rw [sourceSnapshotAssignment_public setup implementation target reference lost]
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, observed]
      rfl
  | activate owner =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp, observed]
      apply congrArg (fun read =>
        ((nativeApplication).observePending owner original.network.pending).map read)
      funext selected
      rfl
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, observed]
      rw [sourceReplayExecution_includePending setup implementation target reference lost
        recalls original handling id]
      rfl
  | application command =>
      have environment : (nativeApplication).environment
          (sourceSnapshotAssignment setup implementation target reference lost
            original.application) command =
          ((nativeApplication).environment original.application command).map
            (sourceSnapshotAssignment setup implementation target reference lost) :=
        sourceSnapshotAssignment_environment setup implementation target reference lost
          implementation.runtime original.application command
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp, observed]
      dsimp only [sourceReplayExecution]
      rw [environment, PMF.map_comp]
      apply congrArg (fun read =>
        ((nativeApplication).environment original.application command).map read)
      funext next
      rfl

/-- At an environment control, the entire counted transition is the exact
pushforward of the original transition, with every original command retained. -/
private theorem sourceReplayExecution_transition
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (original : (nativeApplication).Control) (idle : original.actor = none)
    (handling : ∀ id message, original.execution.network.lookup id = some message →
      (nativeApplication).handle
          (sourceSnapshotAssignment setup implementation target reference lost
            original.execution.application) message =
        ((nativeApplication).handle original.execution.application message).map
          (sourceSnapshotAssignment setup implementation target reference lost)) :
    (nativeApplication).transition nativeInitial implementation.horizon implementation.scheduler
        (some { original with
          execution := sourceReplayExecution setup implementation target reference lost recalls
            original.execution }) (fun _ => none) =
      ((nativeApplication).transition nativeInitial implementation.horizon
        implementation.scheduler (some original) (fun _ => none)).map
        (fun found => found.map fun ending => { ending with
          execution := sourceReplayExecution setup implementation target reference lost recalls
            ending.execution }) := by
  rcases original with ⟨remaining, actor, execution⟩
  dsimp only at idle
  subst actor
  cases remaining with
  | zero =>
      simp only [ReactiveApplication.transition, PMF.pure_map]
      rfl
  | succ remaining =>
      have observed :
          (sourceReplayExecution setup implementation target reference lost recalls
            execution).observeEnvironment nativeApplication =
            execution.observeEnvironment nativeApplication := by
        change
          (⟨execution.network.publicView,
            (sourceSnapshotAssignment setup implementation target reference lost
              execution.application).publicView, execution.receipts⟩ :
                (nativeApplication).EnvironmentView) =
            ⟨execution.network.publicView, execution.application.publicView, execution.receipts⟩
        rw [sourceSnapshotAssignment_public setup implementation target reference lost]
      change
        ((implementation.scheduler execution.environmentRecall
            ((sourceReplayExecution setup implementation target reference lost recalls
              execution).observeEnvironment nativeApplication)).bind fun command =>
          (((sourceReplayExecution setup implementation target reference lost recalls
              execution).environmentStep nativeApplication command).map fun next =>
            some (⟨remaining, command.actor? nativeApplication, next⟩ :
              (nativeApplication).Control))) = _
      rw [observed]
      simp only [ReactiveApplication.transition, PMF.map_bind]
      congr 1
      funext command
      rw [sourceReplayExecution_environment setup implementation target reference lost
        recalls execution handling command, PMF.map_comp, PMF.map_comp]
      rfl

/-- Every actual alias in a proper binding class has the same private
registration and authentic emitted packet. Its recorded raw action may differ. -/
private theorem proper_response_class_effects
    (owner : Player) (execution : (nativeApplication).Execution)
    (counts : PhaseCount.CountRecall implementation.runtime implementation.leaks execution)
    (first second : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : first.val.transmission = some material)
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (value : L.Val payload)
    (packet : material.call.packet = .commitment event handle)
    (prepared : PhaseProposal.bindingPreparation material = some (⟨payload, value⟩ : Raw L))
    (same : PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) first =
      PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) second) :
    (execution.respond nativeApplication owner first.val).application =
        (execution.respond nativeApplication owner second.val).application ∧
      (execution.respond nativeApplication owner first.val).network =
        (execution.respond nativeApplication owner second.val).network := by
  have preparations := congrArg (fun chosen => chosen.val.1) same
  change first.val.transmission.bind PhaseProposal.bindingPreparation =
    second.val.transmission.bind PhaseProposal.bindingPreparation at preparations
  rw [transmitted, Option.bind_some, prepared] at preparations
  cases secondSent : second.val.transmission with
  | none =>
      rw [secondSent, Option.bind_none] at preparations
      cases preparations
  | some other =>
      have otherPrepared : PhaseProposal.bindingPreparation other =
          some (⟨payload, value⟩ : Raw L) := by
        simpa only [secondSent, Option.bind_some] using preparations.symm
      have packets := congrArg (fun chosen => chosen.val.2) same
      change first.val.transmission.map (fun supplied =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (execution.recall owner) (execution.observe nativeApplication owner)
              supplied).payload) =
        second.val.transmission.map (fun supplied =>
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (execution.recall owner) (execution.observe nativeApplication owner)
              supplied).payload)
        at packets
      rw [transmitted, secondSent, Option.map_some, Option.map_some] at packets
      have payloads := Option.some.inj packets
      have wireCalls := congrArg (fun sent : CommitAttemptPacket (serviceGraph setup .concurrent) =>
        sent.packet.call) payloads
      have firstCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope
          implementation.runtime implementation.leaks owner (execution.recall owner)
          (execution.observe nativeApplication owner) material)).payload.call =
          material.call.packet := PhaseCount.maskPacket_call _ _
      have secondCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope
          implementation.runtime implementation.leaks owner (execution.recall owner)
          (execution.observe nativeApplication owner) other)).payload.call =
          other.call.packet := PhaseCount.maskPacket_call _ _
      have otherPacket : other.call.packet = .commitment event handle :=
        secondCall.symm.trans (wireCalls.symm.trans (firstCall.trans packet))
      have calls := properBinding_calls_eq setup material other event handle owner payload binding
        value packet otherPacket prepared otherPrepared
      have submitted : (nativeApplication).submit execution.application owner material =
          (nativeApplication).submit execution.application owner other := by
        change execution.application.submit owner material =
          execution.application.submit owner other
        simp only [PhaseRuntimeState.submit, RecoveryState.submit, calls]
      rw [PhaseCount.localEnvelope_eq_of_recall implementation.runtime implementation.leaks
          execution counts.1 counts.2.1 owner material,
        PhaseCount.localEnvelope_eq_of_recall implementation.runtime implementation.leaks
          execution counts.1 counts.2.1 owner other] at payloads
      change (nativeApplication).packet
          ((nativeApplication).submit execution.application owner material) owner
          (execution.network.known owner) material =
        (nativeApplication).packet
          ((nativeApplication).submit execution.application owner other) owner
          (execution.network.known owner) other at payloads
      constructor
      · simpa only [ReactiveApplication.Execution.respond, transmitted, secondSent]
          using submitted
      · simp only [ReactiveApplication.Execution.respond, transmitted, secondSent]
        rw [payloads]

/-- Opening aliases have the same authenticated call and certificate. Their
unused preparation and evidence syntax cannot alter registration or emission. -/
private theorem opening_response_class_effects
    (owner : Player) (execution : (nativeApplication).Execution)
    (counts : PhaseCount.CountRecall implementation.runtime implementation.leaks execution)
    (first second : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (transmitted : first.val.transmission = some material)
    (event : (serviceGraph setup .concurrent).EventId)
    (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L)
    (packet : material.call.packet = .opening event handle raw)
    (same : PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) first =
      PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) second) :
    (execution.respond nativeApplication owner first.val).application =
        (execution.respond nativeApplication owner second.val).application ∧
      (execution.respond nativeApplication owner first.val).network =
        (execution.respond nativeApplication owner second.val).network := by
  have packets := congrArg (fun chosen => chosen.val.2) same
  change first.val.transmission.map (fun supplied =>
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (execution.recall owner) (execution.observe nativeApplication owner) supplied).payload) =
    second.val.transmission.map (fun supplied =>
      (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
        (execution.recall owner) (execution.observe nativeApplication owner) supplied).payload)
    at packets
  rw [transmitted, Option.map_some] at packets
  cases secondSent : second.val.transmission with
  | none =>
      rw [secondSent, Option.map_none] at packets
      cases packets
  | some other =>
      rw [secondSent, Option.map_some] at packets
      have payloads := Option.some.inj packets
      have wireCalls := congrArg (fun sent : CommitAttemptPacket (serviceGraph setup .concurrent) =>
        sent.packet.call) payloads
      have firstCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope
          implementation.runtime implementation.leaks owner (execution.recall owner)
          (execution.observe nativeApplication owner) material)).payload.call =
          material.call.packet := PhaseCount.maskPacket_call _ _
      have secondCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope
          implementation.runtime implementation.leaks owner (execution.recall owner)
          (execution.observe nativeApplication owner) other)).payload.call =
          other.call.packet := PhaseCount.maskPacket_call _ _
      have otherPacket : other.call.packet = .opening event handle raw :=
        secondCall.symm.trans (wireCalls.symm.trans (firstCall.trans packet))
      have submitted : (nativeApplication).submit execution.application owner material =
          (nativeApplication).submit execution.application owner other := by
        change execution.application.submit owner material =
          execution.application.submit owner other
        simp only [PhaseRuntimeState.submit, RecoveryState.submit, Submission.register,
          packet, otherPacket]
      rw [PhaseCount.localEnvelope_eq_of_recall implementation.runtime implementation.leaks
          execution counts.1 counts.2.1 owner material,
        PhaseCount.localEnvelope_eq_of_recall implementation.runtime implementation.leaks
          execution counts.1 counts.2.1 owner other] at payloads
      change (nativeApplication).packet
          ((nativeApplication).submit execution.application owner material) owner
          (execution.network.known owner) material =
        (nativeApplication).packet
          ((nativeApplication).submit execution.application owner other) owner
          (execution.network.known owner) other at payloads
      constructor
      · simpa only [ReactiveApplication.Execution.respond, transmitted, secondSent]
          using submitted
      · simp only [ReactiveApplication.Execution.respond, transmitted, secondSent]
        rw [payloads]

abbrev RawReplayChoice :=
  Option (Handle (serviceGraph setup .concurrent) × Raw L) ×
    Option (nativeApplication).Action

/-- A script records callbacks in reverse chronological order. The handle in
each lost slot is fixed by its original first registration. -/
def rawReplayLost (choices : List (RawReplayChoice setup implementation))
    (handle : Handle (serviceGraph setup .concurrent)) : Option (Raw L) :=
  choices.findSome? fun choice => choice.1.bind fun draw =>
    if draw.1 = handle then some draw.2 else none

omit [Fintype Player] in
private theorem rawReplayLost_register
    (script : List (RawReplayChoice setup implementation))
    (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L)
    (action : Option (nativeApplication).Action) :
    rawReplayLost setup implementation ((some (handle, raw), action) :: script) =
      Function.update (rawReplayLost setup implementation script) handle (some raw) := by
  classical
  funext candidate
  by_cases same : handle = candidate
  · subst candidate
    simp only [rawReplayLost, List.findSome?_cons, Option.bind_some, ↓reduceIte,
      Function.update_self]
  · simp only [rawReplayLost, List.findSome?_cons, Option.bind_some, same, ↓reduceIte,
      Function.update_of_ne (Ne.symm same)]

/-- Aliases are sampled in the menu at the actual reconstructed input.
The emitted class is fixed, while every raw alias remains a script coordinate. -/
def sourceReplayAliases
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (draw : Option (Handle (serviceGraph setup .concurrent) × Raw L))
    (chosen : PhaseProposal.ResponseClass implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)) :
    PMF (RawReplayChoice setup implementation) :=
  (PMF.splitKernel
    (PhaseProposal.projectResponse implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (PhaseProposal.canonicalResponse implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (PhaseProposal.project_canonicalResponse implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    scale.val scale.property.1 scale.property.2 chosen).map
      (fun response => (draw, some response.val))

theorem sourceReplayAliases_atom
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (draw : Option (Handle (serviceGraph setup .concurrent) × Raw L))
    (chosen : PhaseProposal.ResponseClass implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)) :
    sourceReplayAliases setup implementation scale owner execution draw chosen
        (draw, some response.val) =
      PMF.splitKernel
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner))
        (PhaseProposal.canonicalResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner))
        (PhaseProposal.project_canonicalResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner))
        scale.val scale.property.1 scale.property.2 chosen response := by
  unfold sourceReplayAliases
  apply pmf_map_apply_of_injective
  intro first second equal
  exact Subtype.ext (Option.some.inj (congrArg Prod.snd equal))

private theorem sourceReplayAliases_support
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (draw : Option (Handle (serviceGraph setup .concurrent) × Raw L))
    (chosen : PhaseProposal.ResponseClass implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (choice : RawReplayChoice setup implementation)
    (supported : choice ∈
      (sourceReplayAliases setup implementation scale owner execution draw chosen).support) :
    ∃ response : PhaseProposal.Response implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner),
      choice = (draw, some response.val) ∧
      PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) response = chosen := by
  obtain ⟨response, member, equal⟩ := (PMF.mem_support_map_iff ..).mp supported
  exact ⟨response, equal.symm, PMF.splitKernel_supported _ _ _ _ _ _ _ _ member⟩

omit [Fintype Player] in
private theorem response_not_generated_of_preparation
    (owner : Player) (action : (nativeApplication).Action)
    (prepared : action.transmission.bind PhaseProposal.bindingPreparation ≠ none) :
    ¬ PhaseProposal.GeneratedUnusableBindingAction implementation.runtime implementation.leaks
      owner action := by
  rintro ⟨event, payload, serial, opening, evidence, binding, equal, missing⟩
  apply prepared
  rw [equal]
  simp only [Option.bind_some, PhaseProposal.bindingPreparation, binding, missing,
    Option.map_none]

private theorem response_generated_iff_of_class
    (owner : Player) (execution : (nativeApplication).Execution)
    (first second : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (same : PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) first =
      PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) second) :
    PhaseProposal.GeneratedUnusableBindingAction implementation.runtime implementation.leaks
        owner first.val ↔
      PhaseProposal.GeneratedUnusableBindingAction implementation.runtime implementation.leaks
        owner second.val := by
  classical
  have transfer (left right : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
      (classes : PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner) left =
        PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner) right)
      (generated : PhaseProposal.GeneratedUnusableBindingAction implementation.runtime
        implementation.leaks owner left.val) :
      PhaseProposal.GeneratedUnusableBindingAction implementation.runtime implementation.leaks
        owner right.val := by
    obtain ⟨event, payload, serial, opening, evidence, binding, action, missing⟩ := generated
    let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
      ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
    have transmitted : left.val.transmission = some material :=
      congrArg (fun response : (nativeApplication).Action => response.transmission) action
    have preparations := congrArg (fun chosen => chosen.val.1) classes
    change left.val.transmission.bind PhaseProposal.bindingPreparation =
      right.val.transmission.bind PhaseProposal.bindingPreparation at preparations
    have absent : PhaseProposal.bindingPreparation material = none := by
      simp only [material, PhaseProposal.bindingPreparation, binding, missing, Option.map_none]
    rw [transmitted, Option.bind_some, absent] at preparations
    have packets := congrArg (fun chosen => chosen.val.2) classes
    change left.val.transmission.map (fun supplied =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner) supplied).payload) =
      right.val.transmission.map (fun supplied =>
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (execution.recall owner) (execution.observe nativeApplication owner) supplied).payload)
      at packets
    cases sent : right.val.transmission with
    | none =>
      rw [transmitted, sent, Option.map_some, Option.map_none] at packets
      cases packets
    | some other =>
      rw [transmitted, sent, Option.map_some, Option.map_some] at packets
      have wire := congrArg
        (fun packet : CommitAttemptPacket (serviceGraph setup .concurrent) => packet.packet.call)
          (Option.some.inj packets)
      have firstCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope
          implementation.runtime implementation.leaks owner (execution.recall owner)
            (execution.observe nativeApplication owner) material)).payload.call =
          material.call.packet := PhaseCount.maskPacket_call _ _
      have otherCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope
          implementation.runtime implementation.leaks owner (execution.recall owner)
            (execution.observe nativeApplication owner) other)).payload.call =
          other.call.packet := PhaseCount.maskPacket_call _ _
      have packet : other.call.packet = .commitment event (owner, .prepared serial) :=
        otherCall.symm.trans (wire.symm.trans firstCall)
      have decoded : other.call.opening.bind (fun raw => raw.as? payload) = none := by
        rw [sent, Option.bind_some] at preparations
        have prepared : PhaseProposal.bindingPreparation other = none := preparations.symm
        simp only [PhaseProposal.bindingPreparation, packet, binding] at prepared
        cases known : other.call.opening.bind (fun raw => raw.as? payload) with
        | none => rfl
        | some value => simp only [known, Option.map_some, reduceCtorEq] at prepared
      have otherEq : other =
          ⟨⟨.commitment event (owner, .prepared serial), other.call.opening⟩,
            other.evidence⟩ := by
        cases other with
        | mk call evidence =>
          cases call with
          | mk call opening =>
            change call = .commitment event (owner, .prepared serial) at packet
            cases packet
            rfl
      have actionEq : right.val = ⟨some other⟩ := by
        exact congrArg (fun transmitted => (⟨transmitted⟩ : (nativeApplication).Action)) sent
      refine ⟨event, payload, serial, other.call.opening, other.evidence, binding, ?_, decoded⟩
      rw [actionEq, otherEq]
  exact ⟨transfer first second same, transfer second first same.symm⟩

def sourceReplayLostSlot
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (original : (nativeApplication).Action) :
    Option (Handle (serviceGraph setup .concurrent)) :=
  original.transmission.bind fun material =>
    match material.call.packet with
    | .commitment _ handle =>
      if sourceHandleMeaning setup implementation target reference handle = none then
        some handle else none
    | .opening .. | .malformed .. => none

/- The literal conditional atom retained by a normalized foreign callback. -/
def SourceReplayCallbackAtoms
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) (original : (nativeApplication).Action)
    (kernel : PMF (RawReplayChoice setup implementation)) : Prop :=
  ∀ choice ∈ kernel.support,
    choice.1.map Prod.fst = sourceReplayLostSlot setup implementation target reference original ∧
    ∃ response : PhaseProposal.Response implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner),
      choice.2 = some response.val ∧
      ¬ PhaseProposal.GeneratedUnusableBindingAction implementation.runtime implementation.leaks
        owner response.val ∧
      ((choice.1 = none ∧ kernel choice = sourceReplayAliases setup implementation scale owner
          execution choice.1 (PhaseProposal.projectResponse implementation.runtime
            implementation.leaks implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) choice) ∨
        ∃ (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
          (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
          (key : setup.ProposalRecoveryComponent owner)
          (handle : Handle (serviceGraph setup .concurrent)) (value : L.Val payload),
          (∃ material, original.transmission = some material ∧
            material.call.packet = .commitment event handle) ∧
          phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
            implementation.plan owner event (execution.recall owner)
              (execution.observe nativeApplication owner) = some key ∧
          choice.1 = some (handle, (⟨payload, value⟩ : Raw L)) ∧
          response.val.transmission.bind PhaseProposal.bindingPreparation =
            some (⟨payload, value⟩ : Raw L) ∧
          kernel choice = ((values owner key).map (fun sampled => phaseRecoveryDomainValue setup
              .concurrent event owner payload binding sampled.val.val)) value *
            sourceReplayAliases setup implementation scale owner execution choice.1
              (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                implementation.bounds owner (execution.recall owner)
                  (execution.observe nativeApplication owner) response) choice)

private theorem sourceReplayDrawAliases_atom
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (handle : Handle (serviceGraph setup .concurrent)) (payload : L.Ty)
    (draws : PMF (L.Val payload))
    (canonical : ∀ _value : L.Val payload,
      PhaseProposal.Response implementation.runtime implementation.leaks implementation.bounds
        owner (execution.recall owner) (execution.observe nativeApplication owner))
    (choice : RawReplayChoice setup implementation)
    (supported : choice ∈ (draws.bind (fun value => sourceReplayAliases setup implementation
      scale owner execution (some (handle, (⟨payload, value⟩ : Raw L)))
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner) (canonical value)))).support) :
    ∃ (value : L.Val payload)
      (response : PhaseProposal.Response implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner)),
      choice = (some (handle, (⟨payload, value⟩ : Raw L)), some response.val) ∧
      PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) response =
        PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner) (canonical value) ∧
      (draws.bind (fun value => sourceReplayAliases setup implementation scale owner execution
        (some (handle, (⟨payload, value⟩ : Raw L)))
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner) (canonical value)))) choice =
        draws value * sourceReplayAliases setup implementation scale owner execution choice.1
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) response) choice := by
  classical
  let aliases := fun value => sourceReplayAliases setup implementation scale owner execution
    (some (handle, (⟨payload, value⟩ : Raw L)))
    (PhaseProposal.projectResponse implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner) (canonical value))
  obtain ⟨value, _valueSupported, aliasSupported⟩ := (PMF.mem_support_bind_iff ..).mp supported
  obtain ⟨response, choiceEq, responseClass⟩ := sourceReplayAliases_support setup implementation
    scale owner execution (some (handle, (⟨payload, value⟩ : Raw L))) _ choice aliasSupported
  have unique : ∀ other ∈ draws.support, choice ∈ (aliases other).support → other = value := by
    intro other _otherSupported otherSupported
    obtain ⟨otherResponse, otherEq, _otherClass⟩ := sourceReplayAliases_support setup implementation
      scale owner execution (some (handle, (⟨payload, other⟩ : Raw L))) _ choice otherSupported
    have rawEq : (⟨payload, other⟩ : Raw L) = ⟨payload, value⟩ :=
      congrArg Prod.snd (Option.some.inj (congrArg Prod.fst (otherEq.symm.trans choiceEq)))
    have typed := congrArg (fun raw : Raw L => raw.as? payload) rawEq
    simpa only [Raw.as?_mk, Option.some.injEq] using typed
  refine ⟨value, response, choiceEq, responseClass, ?_⟩
  rw [bind_apply_of_unique_branch draws aliases choice value unique]
  congr 1
  rw [choiceEq]
  rw [responseClass]

private theorem sourceReplayAliases_atoms
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) (original : (nativeApplication).Action)
    (slot : sourceReplayLostSlot setup implementation target reference original = none)
    (canonical : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner))
    (clean : ¬ PhaseProposal.GeneratedUnusableBindingAction implementation.runtime
      implementation.leaks owner canonical.val) :
    SourceReplayCallbackAtoms (setup := setup) (values := values)
      (implementation := implementation) scale owner execution target reference original
      (sourceReplayAliases setup implementation scale owner execution none
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (execution.recall owner)
            (execution.observe nativeApplication owner) canonical)) := by
  intro choice supported
  obtain ⟨response, choiceEq, responseClass⟩ := sourceReplayAliases_support setup implementation
    scale owner execution none _ choice supported
  let chosen := PhaseProposal.projectResponse implementation.runtime implementation.leaks
    implementation.bounds owner (execution.recall owner)
      (execution.observe nativeApplication owner) canonical
  refine ⟨?_, response, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · rw [choiceEq, slot]
    rfl
  · rw [choiceEq]
  · exact (not_congr (response_generated_iff_of_class setup implementation owner execution
      response canonical responseClass)).mpr clean
  · rw [choiceEq]
  · rw [choiceEq]
    let project := PhaseProposal.projectResponse implementation.runtime implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)
    let representative := PhaseProposal.canonicalResponse implementation.runtime
      implementation.leaks
      implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)
    let rightInverse := PhaseProposal.project_canonicalResponse implementation.runtime
      implementation.leaks implementation.bounds owner (execution.recall owner)
        (execution.observe nativeApplication owner)
    have classAtom := congrArg (fun selected => PMF.splitKernel project representative
      rightInverse scale.val scale.property.1 scale.property.2 selected response) responseClass.symm
    have chosenAtom := sourceReplayAliases_atom setup implementation scale owner execution none
      chosen response
    have ownAtom := sourceReplayAliases_atom setup implementation scale owner execution none
      (project response) response
    exact chosenAtom.trans (classAtom.trans ownAtom.symm)

private theorem sourceReplayDrawAliases_atoms
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) (original : (nativeApplication).Action)
    (handle : Handle (serviceGraph setup .concurrent))
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (material : WitnessedSubmission (serviceGraph setup .concurrent))
    (sent : original.transmission = some material)
    (packet : material.call.packet = .commitment event handle)
    (slot : sourceReplayLostSlot setup implementation target reference original = some handle)
    (key : setup.ProposalRecoveryComponent owner)
    (query : phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
      implementation.plan owner event (execution.recall owner)
        (execution.observe nativeApplication owner) = some key)
    (canonical : ∀ _value : L.Val payload,
      PhaseProposal.Response implementation.runtime implementation.leaks implementation.bounds
        owner (execution.recall owner) (execution.observe nativeApplication owner))
    (prepared : ∀ value, (canonical value).val.transmission.bind
      PhaseProposal.bindingPreparation = some (⟨payload, value⟩ : Raw L)) :
    SourceReplayCallbackAtoms (setup := setup) (values := values)
      (implementation := implementation) scale owner execution target reference original
      (((values owner key).map (fun sampled => phaseRecoveryDomainValue setup .concurrent
        event owner payload binding sampled.val.val)).bind (fun value =>
          sourceReplayAliases setup implementation scale owner execution
            (some (handle, (⟨payload, value⟩ : Raw L)))
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (execution.recall owner)
                (execution.observe nativeApplication owner) (canonical value)))) := by
  intro choice supported
  obtain ⟨value, response, choiceEq, responseClass, atom⟩ :=
    sourceReplayDrawAliases_atom setup implementation
    scale owner execution handle payload _ canonical choice supported
  have responsePrepared : response.val.transmission.bind PhaseProposal.bindingPreparation =
      some (⟨payload, value⟩ : Raw L) := by
    have projection := congrArg (fun chosen => chosen.val.1) responseClass
    exact projection.trans (prepared value)
  refine ⟨?_, response, ?_, ?_, Or.inr ⟨event, payload, binding, key, handle, value,
    ⟨material, sent, packet⟩, query, ?_, responsePrepared, atom⟩⟩
  · rw [choiceEq, slot]
    rfl
  · rw [choiceEq]
  · apply response_not_generated_of_preparation setup implementation owner
    rw [responsePrepared]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true]
  · rw [choiceEq]

def SourceReplayPrepared (who : Player) (state : (nativeProtocol).State) : Prop :=
  state.elim True fun control => ∀ owner, owner ≠ who →
    ∀ record ∈ (nativeApplication).recallOwnPlay (control.execution.recall owner),
      ¬ PhaseProposal.GeneratedUnusableBindingAction implementation.runtime implementation.leaks
        owner record.2

theorem sourceReplayPrepared_respond
    (who : Player) (control : (nativeApplication).Control) (owner : Player)
    (response : (nativeApplication).Action)
    (prepared : SourceReplayPrepared setup implementation who (some control))
    (clean : owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingAction implementation.runtime implementation.leaks
        owner response) :
    SourceReplayPrepared setup implementation who (some ⟨control.remaining, none,
      control.execution.respond nativeApplication owner response⟩) := by
  intro observer foreign record member
  by_cases same : observer = owner
  · subst observer
    rw [(nativeApplication).respond_ownPlay] at member
    rcases List.mem_cons.mp member with equal | earlier
    · cases equal
      exact clean foreign
    · exact prepared owner foreign record earlier
  · rw [(nativeApplication).respond_recall_other _ owner observer same] at member
    exact prepared observer foreign record member

theorem sourceReplayPrepared_good
    (who : Player) (history : (nativeProtocol).History)
    (prepared : SourceReplayPrepared setup implementation who history.state) :
    ∀ owner, owner ≠ who →
      ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
        implementation.bounds nativeInitial implementation.horizon implementation.scheduler
          owner history := by
  intro owner foreign generated
  obtain ⟨record, member, bad⟩ := generated
  change record ∈ ((nativeMenu).signals nativeInitial implementation.horizon
    implementation.scheduler).ownPlay owner history.trace at member
  rw [← (nativeMenu).ownPlay_toRawTrace nativeInitial implementation.horizon
    implementation.scheduler owner history.trace,
    (nativeApplication).trace_ownPlay] at member
  cases present : history.state with
  | none =>
    simp only [ReactiveApplication.recallAt, present, ReactiveApplication.recallOwnPlay,
      ReactiveApplication.ownPlayFrom, List.not_mem_nil] at member
  | some control =>
    simp only [ReactiveApplication.recallAt, present] at member
    rw [present] at prepared
    exact prepared owner foreign record member bad

/-- Raw callbacks keep their own actual aliases. The remaining control,
network, receipts, service history and focal raw recall are literal. -/
def RawReplayState
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (original actual : (nativeProtocol).History) : Prop :=
  match original.state, actual.state with
  | none, none => True
  | some first, some second =>
      second.remaining = first.remaining ∧ second.actor = first.actor ∧
        second.execution = sourceReplayExecution setup implementation target reference lost
          second.execution.recall first.execution ∧
        second.execution.recall who = first.execution.recall who ∧
        second.execution.observe nativeApplication who =
          first.execution.observe nativeApplication who
  | _, _ => False

/-- The state relation preserves the complete mechanical observation,
including freshness at every raw prepared handle. -/
theorem RawReplayState.mechanicalProjection
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (original actual : (nativeProtocol).History)
    (related : RawReplayState setup implementation who target reference lost original actual) :
    mechanicalProjection setup implementation who actual.state =
      mechanicalProjection setup implementation who original.state := by
  classical
  cases originalState : original.state with
  | none =>
      cases actualState : actual.state with
      | none => rfl
      | some second =>
          simp only [RawReplayState, originalState, actualState] at related
  | some first =>
      cases actualState : actual.state with
      | none => simp only [RawReplayState, originalState, actualState] at related
      | some second =>
          simp only [RawReplayState, originalState, actualState] at related
          obtain ⟨remaining, actor, execution, recalled, observed⟩ := related
          have visible : second.execution.application.publicView =
              first.execution.application.publicView := by
            exact (congrArg (fun state : (nativeApplication).Execution =>
              state.application.publicView) execution).trans
                (sourceSnapshotAssignment_public setup implementation target reference lost _)
          have network := congrArg (fun state : (nativeApplication).Execution => state.network)
            execution
          change second.execution.network = first.execution.network at network
          have receipts := congrArg (fun state : (nativeApplication).Execution => state.receipts)
            execution
          change second.execution.receipts = first.execution.receipts at receipts
          have service := congrArg
            (fun state : (nativeApplication).Execution => state.environmentRecall) execution
          change second.execution.environmentRecall = first.execution.environmentRecall at service
          have candidates : (fun owner serial => decide
              (second.execution.application.current.native.candidates.lookup
                (owner, .prepared serial) = .fresh)) =
              (fun owner serial => decide
                (first.execution.application.current.native.candidates.lookup
                  (owner, .prepared serial) = .fresh)) := by
            rw [execution]
            funext owner serial
            simp only [sourceReplayExecution, sourceSnapshotAssignment, sourceSnapshotState,
              State.swap_candidates, HiddenSwap.lookup_candidates, swapCandidate_eq_fresh_iff]
          change some (second.remaining, second.actor, second.execution.application.publicView,
            second.execution.network.publicView, second.execution.receipts,
            second.execution.observe nativeApplication who,
            (fun owner serial => decide
              (second.execution.application.current.native.candidates.lookup
                (owner, .prepared serial) = .fresh)),
            second.execution.environmentRecall, second.execution.recall who) =
              some (first.remaining, first.actor, first.execution.application.publicView,
                first.execution.network.publicView, first.execution.receipts,
                first.execution.observe nativeApplication who,
                (fun owner serial => decide
                  (first.execution.application.current.native.candidates.lookup
                    (owner, .prepared serial) = .fresh)),
                first.execution.environmentRecall, first.execution.recall who)
          rw [remaining, actor, visible, network, receipts, observed, candidates, service, recalled]

open Classical in
/-- Append only a genuine legal, supported transition to the actual prefix. -/
def sourceReplayAppend
    (actual : (nativeProtocol).History) (next : (nativeProtocol).State)
    (chosen : Player → Option (nativeApplication).Action) :
    Option (nativeProtocol).History :=
  if offered : (nativeProtocol).Legal actual.state chosen then
    if moved : next ∈ ((nativeProtocol).step actual.state ⟨chosen, offered⟩).support then
      some (actual.extend offered moved)
    else none
  else none

theorem sourceReplayAppend_supported
    (actual : (nativeProtocol).History) (next : (nativeProtocol).State)
    (chosen : Player → Option (nativeApplication).Action)
    (offered : (nativeProtocol).Legal actual.state chosen)
    (moved : next ∈ ((nativeProtocol).step actual.state ⟨chosen, offered⟩).support) :
    sourceReplayAppend setup implementation actual next chosen =
      some (actual.extend offered moved) := by
  classical
  simp only [sourceReplayAppend, dite_eq_left offered, dite_eq_left moved]

open Classical in
/-- Literal raw replay: callbacks execute their actual chosen aliases and
environment steps retain the original network and service observations.
Each returned history includes proofs of legality and transition support. -/
def sourceRawReplay
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) :
    (nativeProtocol).History → List (RawReplayChoice setup implementation) →
      Option (nativeProtocol).History
  | ⟨_, .start⟩, [] => some (nativeProtocol).initHistory
  | ⟨_, .start⟩, _ :: _ => none
  | ⟨_, .extend _ _ _ _⟩, [] => none
  | ⟨after, .extend prior joint _legal _realized⟩, choice :: earlier =>
      (sourceRawReplay who target reference ⟨_, prior⟩ earlier).bind fun actual =>
        match (⟨_, prior⟩ : (nativeProtocol).History).state with
        | none =>
            match target.state with
            | none => none
            | some current =>
                sourceReplayAppend setup implementation actual
                  (some ⟨implementation.horizon, none,
                  ReactiveApplication.Execution.initial nativeApplication
                    (PhaseRuntimeState.initial implementation.plan
                      (encodeInputs (ProtocolState.base setup.program current.point)))⟩)
                  (fun _ => none)
        | some original =>
            match original.actor with
            | some owner =>
                match actual.state with
                | none => none
                | some before =>
                    let response := if owner = who then joint owner else choice.2
                    response.bind fun action =>
                      sourceReplayAppend setup implementation actual (some { before with
                        actor := none
                        execution := before.execution.respond nativeApplication owner action })
                        (fun player => if player = owner then some action else none)
            | none =>
                match actual.state, after with
                | some before, some ending =>
                    let execution := sourceReplayExecution setup implementation target reference
                      (rawReplayLost setup implementation (choice :: earlier))
                      before.execution.recall ending.execution
                    sourceReplayAppend setup implementation actual
                      (some { ending with execution := execution }) (fun _ => none)
                | _, _ => none

/-- Replay initializes from the target's entire correlated input tuple,
using support of its actual source initialization. -/
theorem sourceRawReplay_initialize
    (who : Player) (reference : (nativeApplication).Control)
    (current : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some current))
    (after : (nativeProtocol).State)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal none joint)
    (moved : after ∈ ((nativeProtocol).step none ⟨joint, legal⟩).support) :
    ∃ actual : (nativeProtocol).History,
      sourceRawReplay setup implementation who ⟨some current, targetTrace⟩ reference
          ⟨after, Trace.start.extend joint legal moved⟩ [(none, none)] = some actual ∧
      actual.state = some ⟨implementation.horizon, none,
        ReactiveApplication.Execution.initial nativeApplication
          (PhaseRuntimeState.initial implementation.plan
            (encodeInputs (ProtocolState.base setup.program current.point)))⟩ ∧
      mechanicalWord setup implementation who actual.trace =
        [⟨mechanicalProjection setup implementation who none, none, rfl⟩,
          ⟨mechanicalProjection setup implementation who (some ⟨implementation.horizon, none,
              ReactiveApplication.Execution.initial nativeApplication
                (PhaseRuntimeState.initial implementation.plan
                  (encodeInputs (ProtocolState.base setup.program current.point)))⟩),
            some ⟨implementation.horizon, none,
              ReactiveApplication.Execution.initial nativeApplication
                (PhaseRuntimeState.initial implementation.plan
                  (encodeInputs (ProtocolState.base setup.program current.point)))⟩, rfl⟩] := by
  classical
  let next : (nativeApplication).Control := ⟨implementation.horizon, none,
    ReactiveApplication.Execution.initial nativeApplication
      (PhaseRuntimeState.initial implementation.plan
        (encodeInputs (ProtocolState.base setup.program current.point)))⟩
  have offered : (nativeProtocol).Legal none (fun _ => none) := by
    constructor
    · simp only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal,
        not_false_eq_true]
    · intro owner
      simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor]
  have supported : some next ∈
      ((nativeProtocol).step none ⟨fun _ => none, offered⟩).support := by
    change _ ∈ (((setup.initialLaw.map fun theta =>
      PhaseRuntimeState.initial implementation.plan (encodeInputs theta)).map fun state =>
        some (⟨implementation.horizon, none,
          ReactiveApplication.Execution.initial nativeApplication state⟩ :
          (nativeApplication).Control))).support
    apply (PMF.mem_support_map_iff ..).mpr
    refine ⟨_, (PMF.mem_support_map_iff ..).mpr ?_, rfl⟩
    exact ⟨_, (source_initial_base_supported setup current targetTrace).1, rfl⟩
  let actual := (nativeProtocol).initHistory.extend offered supported
  refine ⟨actual, ?_, rfl, rfl⟩
  simp only [sourceRawReplay, Option.bind_some]
  exact sourceReplayAppend_supported setup implementation (nativeProtocol).initHistory
    (some next) (fun _ => none) offered supported

/-- Complete pending observation and the public sample result identify an
actual environment successor at its literal preceding execution. -/
private theorem sourceReplay_environment_result_unique
    (operational : implementation.Operational)
    (before first second : (nativeApplication).Execution)
    (command : (nativeApplication).Command)
    (left : first ∈ (before.environmentStep nativeApplication command).support)
    (right : second ∈ (before.environmentStep nativeApplication command).support)
    (same : first.observeEnvironment nativeApplication =
      second.observeEnvironment nativeApplication) : first = second := by
  classical
  cases command with
  | activate owner =>
      have complete : (nativeApplication).observePending =
          MessageNetwork.completePendingObservation := operational.completePending
      rw [ReactiveApplication.Execution.activation_samples, complete] at left right
      simp only [MessageNetwork.completePendingObservation, PMF.pure_map,
        PMF.mem_support_pure_iff] at left right
      exact left.trans right.symm
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at left right
      exact left.trans right.symm
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at left right
      exact left.trans right.symm
  | application command =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp,
        Function.comp_def] at left right
      obtain ⟨firstState, firstSupported, rfl⟩ := (PMF.mem_support_map_iff ..).mp left
      obtain ⟨secondState, secondSupported, rfl⟩ := (PMF.mem_support_map_iff ..).mp right
      have states : firstState.publicView = secondState.publicView :=
        congrArg ReactiveApplication.EnvironmentView.application same
      have equal := PhaseRuntimeState.environment_eq_of_publicView implementation.runtime
        before.application firstState secondState command firstSupported secondSupported states
      cases equal
      rfl

/-- Two supported idle transitions from the same actual prefix coincide if
their next mechanical states coincide. This reads the actual command from
the recorded environment word, including complete activation observations. -/
theorem sourceReplay_environment_step_unique
    (operational : implementation.Operational) (who : Player)
    (before first second : (nativeApplication).Control)
    (idle : before.actor = none)
    (firstJoint secondJoint : Player → Option (nativeApplication).Action)
    (left : some first ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some before) firstJoint).support)
    (right : some second ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some before) secondJoint).support)
    (same : mechanicalProjection setup implementation who (some first) =
      mechanicalProjection setup implementation who (some second)) : first = second := by
  classical
  obtain ⟨_remaining, _actor, views, records⟩ :=
    mechanicalProjection_environment setup implementation who first second same
  rcases before with ⟨remaining, actor, execution⟩
  dsimp only at idle
  subst actor
  cases remaining with
  | zero =>
      simp only [ReactiveApplication.transition, PMF.mem_support_pure_iff,
        Option.some.injEq] at left right
      exact left.trans right.symm
  | succ remaining =>
      change some first ∈ ((implementation.scheduler execution.environmentRecall
        (execution.observeEnvironment nativeApplication)).bind fun command =>
          (execution.environmentStep nativeApplication command).map fun ending =>
            some (⟨remaining, command.actor? nativeApplication, ending⟩ :
              (nativeApplication).Control)).support at left
      change some second ∈ ((implementation.scheduler execution.environmentRecall
        (execution.observeEnvironment nativeApplication)).bind fun command =>
          (execution.environmentStep nativeApplication command).map fun ending =>
            some (⟨remaining, command.actor? nativeApplication, ending⟩ :
              (nativeApplication).Control)).support at right
      obtain ⟨firstCommand, _firstSelected, firstReached⟩ :=
        (PMF.mem_support_bind_iff ..).mp left
      obtain ⟨firstExecution, firstMoved, firstEqual⟩ :=
        (PMF.mem_support_map_iff ..).mp firstReached
      obtain ⟨secondCommand, _secondSelected, secondReached⟩ :=
        (PMF.mem_support_bind_iff ..).mp right
      obtain ⟨secondExecution, secondMoved, secondEqual⟩ :=
        (PMF.mem_support_map_iff ..).mp secondReached
      cases Option.some.inj firstEqual
      cases Option.some.inj secondEqual
      have commands : firstCommand = secondCommand := by
        rw [(nativeApplication).environmentStep_environmentRecall execution firstExecution
          firstCommand firstMoved,
          (nativeApplication).environmentStep_environmentRecall execution secondExecution
            secondCommand secondMoved] at records
        exact congrArg ReactiveApplication.EnvironmentEntry.command
          (List.singleton_inj.mp (List.append_cancel_left records))
      subst secondCommand
      have ending := sourceReplay_environment_result_unique setup implementation operational
        execution firstExecution secondExecution firstCommand firstMoved secondMoved views
      cases ending
      rfl

/-- An environment extension cannot fail once the preceding actual prefix
has its assigned application. Its support is transported from the original
transition, including all original network and receipt observations. -/
theorem sourceRawReplay_environment_extend
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (before after : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (idle : before.actor = none)
    (script : List (RawReplayChoice setup implementation))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (actualControl : (nativeApplication).Control)
    (assigned : actualControl = { before with
      execution := sourceReplayExecution setup implementation target reference
        (rawReplayLost setup implementation script) recalls before.execution })
    (actual : (nativeProtocol).Trace (some actualControl))
    (replayed : sourceRawReplay setup implementation who target reference
        ⟨some before, prior⟩ script = some ⟨_, actual⟩)
    (_image : SourceReplayImage setup implementation target reference referenceTrace
      (rawReplayLost setup implementation script) who before)
    (nextImage : SourceReplayImage setup implementation target reference referenceTrace
      (rawReplayLost setup implementation script) who after)
    (past : recalls who = before.execution.recall who)
    (word : mechanicalWord setup implementation who actual =
      mechanicalWord setup implementation who prior) :
    ∃ next : (nativeProtocol).History,
      sourceRawReplay setup implementation who target reference
          ⟨some after, prior.extend joint legal moved⟩ ((none, none) :: script) = some next ∧
      next.state = some { after with
        execution := sourceReplayExecution setup implementation target reference
          (rawReplayLost setup implementation script) recalls after.execution } ∧
      TracePrefix actual next.trace ∧
      RawReplayState setup implementation who target reference
        (rawReplayLost setup implementation script)
        ⟨some after, prior.extend joint legal moved⟩ next ∧
      mechanicalWord setup implementation who next.trace =
        mechanicalWord setup implementation who (prior.extend joint legal moved) := by
  subst actualControl
  classical
  let lost := rawReplayLost setup implementation script
  let first : (nativeApplication).Control := { before with
    execution := sourceReplayExecution setup implementation target reference lost recalls
      before.execution }
  let last : (nativeApplication).Control := { after with
    execution := sourceReplayExecution setup implementation target reference lost recalls
      after.execution }
  have offered : (nativeProtocol).Legal (some first) (fun _ => none) := by
    constructor
    · simpa only [ReactiveApplication.ResponseMenu.protocol,
        ReactiveApplication.terminal, first] using legal.1
    · intro owner
      simp only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
        Option.bind_some, first, idle]
      simp
  have originalMoved : some after ∈
      ((nativeApplication).transition nativeInitial implementation.horizon
        implementation.scheduler (some before) (fun _ => none)).support := by
    change _ ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some before) joint).support at moved
    simpa only [ReactiveApplication.transition, idle] using moved
  have transported : some last ∈
      ((nativeProtocol).step (some first) ⟨fun _ => none, offered⟩).support := by
    change _ ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some first) (fun _ => none)).support
    rw [sourceReplayExecution_transition setup implementation target reference lost recalls
      before idle _image.handling]
    exact (PMF.mem_support_map_iff ..).mpr ⟨some after, originalMoved, rfl⟩
  let next : (nativeProtocol).History := ⟨some last,
    actual.extend (fun _ => none) offered transported⟩
  have stable : after.execution.recall = before.execution.recall := by
    rcases before with ⟨remaining, actor, execution⟩
    dsimp only at idle originalMoved
    subst actor
    cases remaining with
    | zero =>
        simp only [ReactiveApplication.transition, PMF.mem_support_pure_iff,
          Option.some.injEq] at originalMoved
        rw [originalMoved]
    | succ remaining =>
        change some after ∈ ((implementation.scheduler execution.environmentRecall
          (execution.observeEnvironment nativeApplication)).bind fun command =>
            (execution.environmentStep nativeApplication command).map fun ending =>
              some (⟨remaining, command.actor? nativeApplication, ending⟩ :
                (nativeApplication).Control)).support at originalMoved
        obtain ⟨command, _, reached⟩ := (PMF.mem_support_bind_iff ..).mp originalMoved
        obtain ⟨ending, supported, equal⟩ := (PMF.mem_support_map_iff ..).mp reached
        cases Option.some.inj equal
        exact (nativeApplication).environmentStep_recall execution ending command supported
  have pastAfter : recalls who = after.execution.recall who :=
    past.trans (congrFun stable who).symm
  have related : RawReplayState setup implementation who target reference lost
      ⟨some after, prior.extend joint legal moved⟩ next := by
    change last.remaining = after.remaining ∧ last.actor = after.actor ∧
      last.execution = sourceReplayExecution setup implementation target reference lost
        last.execution.recall after.execution ∧
      last.execution.recall who = after.execution.recall who ∧
      last.execution.observe nativeApplication who = after.execution.observe nativeApplication who
    exact ⟨rfl, rfl, rfl, pastAfter, nextImage.focalView recalls pastAfter⟩
  refine ⟨next, ?_, rfl, TracePrefix.extend TracePrefix.refl _ _ _, related, ?_⟩
  · have padding : rawReplayLost setup implementation ((none, none) :: script) = lost := rfl
    simp only [sourceRawReplay, replayed, Option.bind_some, idle, padding]
    exact sourceReplayAppend_supported setup implementation ⟨some first, actual⟩ (some last)
      (fun _ => none) offered transported
  · have projected :
        (⟨mechanicalProjection setup implementation who (some last), some last, rfl⟩ :
          Set.range (mechanicalProjection setup implementation who)) =
        ⟨mechanicalProjection setup implementation who (some after), some after, rfl⟩ :=
      Subtype.ext (RawReplayState.mechanicalProjection setup implementation who target reference
        lost _ _ related)
    change mechanicalWord setup implementation who actual ++ [_] =
      mechanicalWord setup implementation who prior ++ [_]
    rw [word, projected]

/-- A sampled response is executed at its actual input. Menu membership
supplies legality and the callback transition is deterministic, so this
branch constructs the actual extension rather than assuming its support. -/
theorem sourceRawReplay_callback_extend
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference before : (nativeApplication).Control)
    (after : (nativeProtocol).State)
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (owner : Player) (acting : before.actor = some owner)
    (script : List (RawReplayChoice setup implementation))
    (choice : RawReplayChoice setup implementation)
    (actualControl : (nativeApplication).Control)
    (actual : (nativeProtocol).Trace (some actualControl))
    (replayed : sourceRawReplay setup implementation who target reference
      ⟨some before, prior⟩ script = some ⟨some actualControl, actual⟩)
    (actualActor : actualControl.actor = some owner)
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (actualControl.execution.recall owner)
        (actualControl.execution.observe nativeApplication owner))
    (selected : (if owner = who then joint owner else choice.2) = some response.val) :
    ∃ next : (nativeProtocol).History,
      sourceRawReplay setup implementation who target reference
          ⟨after, prior.extend joint legal moved⟩ (choice :: script) = some next ∧
      next.state = some { actualControl with
        actor := none
        execution := actualControl.execution.respond nativeApplication owner response.val } ∧
      TracePrefix actual next.trace ∧
      mechanicalWord setup implementation who next.trace =
        mechanicalWord setup implementation who actual ++
          [⟨mechanicalProjection setup implementation who next.state, next.state, rfl⟩] := by
  classical
  let chosen : Player → Option (nativeApplication).Action :=
    fun player => if player = owner then some response.val else none
  let ending : (nativeApplication).Control := { actualControl with
    actor := none
    execution := actualControl.execution.respond nativeApplication owner response.val }
  have offered : (nativeProtocol).Legal (some actualControl) chosen := by
    constructor
    · simp only [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.terminal,
        actualActor, reduceCtorEq, and_false, not_false_eq_true]
    · intro player
      by_cases same : player = owner
      · subst player
        simpa only [chosen, ↓reduceIte, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor, Option.bind_some, actualActor,
          ReactiveApplication.ResponseMenu.available, PhaseCount.onePacketMenu,
          Finset.mem_coe, true_and] using response.property
      · simp only [chosen, same, ↓reduceIte, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor, Option.bind_some, actualActor,
          Option.some.injEq, not_false_eq_true, Ne.symm same]
  have transported : some ending ∈
      ((nativeProtocol).step (some actualControl) ⟨chosen, offered⟩).support := by
    change _ ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some actualControl) chosen).support
    simp only [ReactiveApplication.transition, actualActor, chosen, ↓reduceIte,
      Option.getD_some, PMF.mem_support_pure_iff]
    rfl
  let next : (nativeProtocol).History := ⟨some ending,
    actual.extend chosen offered transported⟩
  refine ⟨next, ?_, rfl, TracePrefix.extend TracePrefix.refl _ _ _, rfl⟩
  simp only [sourceRawReplay, replayed, Option.bind_some, acting, selected]
  exact sourceReplayAppend_supported setup implementation ⟨some actualControl, actual⟩
    (some ending) chosen offered transported

/-- The actual focal callback preserves its full raw input and action. The
next static source image then supplies its literal next observation. -/
theorem sourceRawReplay_focal_extend
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (before after : (nativeApplication).Control)
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (onward : TracePrefix (prior.extend joint legal moved) referenceTrace)
    (acting : before.actor = some who)
    (script : List (RawReplayChoice setup implementation))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (actualControl : (nativeApplication).Control)
    (assigned : actualControl = { before with
      execution := sourceReplayExecution setup implementation target reference
        (rawReplayLost setup implementation script) recalls before.execution })
    (actual : (nativeProtocol).Trace (some actualControl))
    (replayed : sourceRawReplay setup implementation who target reference
        ⟨some before, prior⟩ script = some ⟨_, actual⟩)
    (image : SourceReplayImage setup implementation target reference referenceTrace
      (rawReplayLost setup implementation script) who before)
    (nextImage : SourceReplayImage setup implementation target reference referenceTrace
      (rawReplayLost setup implementation script) who after)
    (past : recalls who = before.execution.recall who)
    (word : mechanicalWord setup implementation who actual =
      mechanicalWord setup implementation who prior) :
    ∃ next : (nativeProtocol).History,
      sourceRawReplay setup implementation who target reference
          ⟨some after, prior.extend joint legal moved⟩ ((none, none) :: script) = some next ∧
      TracePrefix actual next.trace ∧
      RawReplayState setup implementation who target reference
        (rawReplayLost setup implementation script)
        ⟨some after, prior.extend joint legal moved⟩ next ∧
      mechanicalWord setup implementation who next.trace =
        mechanicalWord setup implementation who (prior.extend joint legal moved) := by
  subst actualControl
  classical
  let lost := rawReplayLost setup implementation script
  let actualControl : (nativeApplication).Control := { before with
    execution := sourceReplayExecution setup implementation target reference lost recalls
      before.execution }
  obtain ⟨action, chosen⟩ : ∃ action, joint who = some action := by
    cases selected : joint who with
    | none =>
        have absent := legal.2 who
        rw [selected] at absent
        exact (absent (by change before.actor = some who; exact acting)).elim
    | some action => exact ⟨action, rfl⟩
  have originalOffered : action ∈ PhaseCount.onePacketActions implementation.runtime
      implementation.leaks implementation.bounds who (before.execution.recall who)
        (before.execution.observe nativeApplication who) := by
    have localLegal := legal.2 who
    rw [chosen] at localLegal
    exact localLegal.2
  have observed := image.focalView recalls past
  have actualOffered : action ∈ PhaseCount.onePacketActions implementation.runtime
      implementation.leaks implementation.bounds who (actualControl.execution.recall who)
        (actualControl.execution.observe nativeApplication who) := by
    change action ∈ PhaseCount.onePacketActions implementation.runtime implementation.leaks
      implementation.bounds who (recalls who) _
    rw [past, observed]
    exact originalOffered
  let response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds who (actualControl.execution.recall who)
        (actualControl.execution.observe nativeApplication who) := ⟨action, actualOffered⟩
  obtain ⟨next, replay, nextState, retained, suffix⟩ := sourceRawReplay_callback_extend
    setup implementation who target reference before (some after) prior joint legal moved
      who acting script (none, none) actualControl actual replayed (by exact acting) response
        (by simp only [ite_true, chosen]; rfl)
  have afterEq : after = { before with
      actor := none
      execution := before.execution.respond nativeApplication who action } := by
    have reached := moved
    change some after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some before) joint).support at reached
    simpa only [ReactiveApplication.transition, acting, chosen, Option.getD_some,
      PMF.mem_support_pure_iff, Option.some.injEq] using reached
  have originalCounts := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler prior)
  have actualCounts := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler actual)
  have responded := sourceReplayExecution_focal_respond setup implementation target reference lost
    recalls before.execution who originalCounts actualCounts past observed action
      (image.focalAction prior (some after) joint legal moved onward action acting chosen)
  dsimp only at responded
  let execution := actualControl.execution.respond nativeApplication who action
  have executionEq : execution = sourceReplayExecution setup implementation target reference lost
      execution.recall after.execution := by
    simpa only [execution, actualControl, afterEq] using responded.1
  have recalled : execution.recall who = after.execution.recall who := by
    simpa only [execution, actualControl, afterEq] using responded.2
  have viewed : execution.observe nativeApplication who =
      after.execution.observe nativeApplication who := by
    rw [executionEq]
    exact nextImage.focalView execution.recall recalled
  have related : RawReplayState setup implementation who target reference lost
      ⟨some after, prior.extend joint legal moved⟩ next := by
    simp only [RawReplayState, nextState]
    exact ⟨by simp only [actualControl, afterEq], by simp only [afterEq],
      executionEq, recalled, viewed⟩
  refine ⟨next, replay, retained, related, ?_⟩
  have projected :
      (⟨mechanicalProjection setup implementation who next.state, next.state, rfl⟩ :
        Set.range (mechanicalProjection setup implementation who)) =
      ⟨mechanicalProjection setup implementation who (some after), some after, rfl⟩ :=
    Subtype.ext (RawReplayState.mechanicalProjection setup implementation who target reference
      lost _ _ related)
  change mechanicalWord setup implementation who next.trace =
    mechanicalWord setup implementation who prior ++ [_]
  rw [suffix, word, projected]

/-- A foreign callback with the assigned application effect and authentic
packet extension the actual replay and retains the focal input and word. -/
private theorem sourceRawReplay_foreign_extend
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference before after : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (owner : Player) (foreign : owner ≠ who) (acting : before.actor = some owner)
    (first : (nativeApplication).Action) (selected : joint owner = some first)
    (script : List (RawReplayChoice setup implementation))
    (choice : RawReplayChoice setup implementation)
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (lostEq : rawReplayLost setup implementation (choice :: script) = lost)
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (actualControl : (nativeApplication).Control)
    (assigned : actualControl = { before with
      execution := sourceReplayExecution setup implementation target reference lost recalls
        before.execution })
    (actual : (nativeProtocol).Trace (some actualControl))
    (replayed : sourceRawReplay setup implementation who target reference
      ⟨some before, prior⟩ script = some ⟨some actualControl, actual⟩)
    (past : recalls who = before.execution.recall who)
    (word : mechanicalWord setup implementation who actual =
      mechanicalWord setup implementation who prior)
    (nextImage : SourceReplayImage setup implementation target reference referenceTrace
      lost who after)
    (response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (actualControl.execution.recall owner)
        (actualControl.execution.observe nativeApplication owner))
    (chosen : choice.2 = some response.val)
    (application : (actualControl.execution.respond nativeApplication owner
      response.val).application =
      sourceSnapshotAssignment setup implementation target reference lost
        (before.execution.respond nativeApplication owner first).application)
    (network : (actualControl.execution.respond nativeApplication owner response.val).network =
      (before.execution.respond nativeApplication owner first).network) :
    ∃ history : (nativeProtocol).History,
      sourceRawReplay setup implementation who target reference
          ⟨some after, prior.extend joint legal moved⟩ (choice :: script) = some history ∧
        TracePrefix actual history.trace ∧
        RawReplayState setup implementation who target reference
          (rawReplayLost setup implementation (choice :: script))
            ⟨some after, prior.extend joint legal moved⟩ history ∧
        mechanicalWord setup implementation who history.trace =
          mechanicalWord setup implementation who (prior.extend joint legal moved) := by
  classical
  obtain ⟨history, replay, nextState, retained, suffix⟩ := sourceRawReplay_callback_extend
    setup implementation who target reference before (some after) prior joint legal moved owner
      acting script choice actualControl actual replayed (by rw [assigned]; exact acting) response
        (by simp only [foreign, ↓reduceIte, chosen])
  have afterEq : after = { before with
      actor := none
      execution := before.execution.respond nativeApplication owner first } := by
    have reached := moved
    change some after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some before) joint).support at reached
    simpa only [ReactiveApplication.transition, acting, selected, Option.getD_some,
      PMF.mem_support_pure_iff, Option.some.injEq] using reached
  let execution := actualControl.execution.respond nativeApplication owner response.val
  have executionEq : execution = sourceReplayExecution setup implementation target reference lost
      execution.recall after.execution := by
    change (⟨execution.application, execution.network, execution.receipts,
        execution.recall, execution.environmentRecall⟩ : (nativeApplication).Execution) =
      ⟨sourceSnapshotAssignment setup implementation target reference lost
          after.execution.application, after.execution.network, after.execution.receipts,
        execution.recall, after.execution.environmentRecall⟩
    rw [show execution.application = sourceSnapshotAssignment setup implementation target reference
      lost after.execution.application from by simpa only [afterEq] using application]
    rw [show execution.network = after.execution.network from by
      simpa only [afterEq] using network]
    congr 1
    · simp only [execution, ReactiveApplication.Execution.respond, assigned, sourceReplayExecution,
        afterEq]
    · simp only [execution, ReactiveApplication.Execution.respond, assigned, sourceReplayExecution,
        afterEq]
  have recalled : execution.recall who = after.execution.recall who := by
    simp only [execution, ReactiveApplication.Execution.respond, Ne.symm foreign, ↓reduceIte,
      assigned, sourceReplayExecution, afterEq]
    exact past
  have viewed : execution.observe nativeApplication who =
      after.execution.observe nativeApplication who := by
    rw [executionEq]
    exact nextImage.focalView execution.recall recalled
  have related : RawReplayState setup implementation who target reference lost
      ⟨some after, prior.extend joint legal moved⟩ history := by
    simp only [RawReplayState, nextState]
    exact ⟨by simp only [assigned, afterEq], by simp only [afterEq], executionEq, recalled, viewed⟩
  refine ⟨history, replay, retained, ?_, ?_⟩
  · rw [lostEq]
    exact related
  · have projected :
      (⟨mechanicalProjection setup implementation who history.state, history.state, rfl⟩ :
        Set.range (mechanicalProjection setup implementation who)) =
      ⟨mechanicalProjection setup implementation who (some after), some after, rfl⟩ :=
        Subtype.ext (RawReplayState.mechanicalProjection setup implementation who target reference
          lost _ _ related)
    change mechanicalWord setup implementation who history.trace =
      mechanicalWord setup implementation who prior ++ [_]
    rw [suffix, word, projected]

/-- A proper foreign callback samples aliases in its reconstructed menu and
executes the assigned value. Both menu membership and raw transition support
are constructed from the actual two prefixes. -/
private theorem sourceRawReplay_proper_extend
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference before after : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (onward : TracePrefix (prior.extend joint legal moved) referenceTrace)
    (owner : Player) (foreign : owner ≠ who) (acting : before.actor = some owner)
    (script : List (RawReplayChoice setup implementation))
    (draw : Option (Handle (serviceGraph setup .concurrent) × Raw L))
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (lostEq : lost = rawReplayLost setup implementation ((draw, none) :: script))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (actualControl : (nativeApplication).Control)
    (assigned : actualControl = { before with
      execution := sourceReplayExecution setup implementation target reference lost recalls
        before.execution })
    (actual : (nativeProtocol).Trace (some actualControl))
    (replayed : sourceRawReplay setup implementation who target reference
      ⟨some before, prior⟩ script = some ⟨some actualControl, actual⟩)
    (past : recalls who = before.execution.recall who)
    (word : mechanicalWord setup implementation who actual =
      mechanicalWord setup implementation who prior)
    (nextImage : SourceReplayImage setup implementation target reference referenceTrace
      lost who after)
    (scale : Set.Icc (0 : ℝ) 1)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, event⟩)
    (serial : Nat) (old next : L.Val payload)
    (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (selected : joint owner = some
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), some ⟨payload, old⟩⟩, evidence⟩⟩)
    (allValues : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈
      implementation.bounds.values)
    (meaning : (sourceHandleMeaning setup implementation target reference
        (owner, .prepared serial)).orElse (fun _ => lost (owner, .prepared serial)) =
      some (⟨payload, next⟩ : Raw L)) :
    ∃ canonical : PhaseProposal.Response implementation.runtime implementation.leaks
        implementation.bounds owner (actualControl.execution.recall owner)
          (actualControl.execution.observe nativeApplication owner),
      canonical.val = phaseBindingResponse implementation.runtime implementation.leaks owner
        event payload (.success next) serial ∧
      ∀ choice ∈ (sourceReplayAliases setup implementation scale owner actualControl.execution
          draw (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (actualControl.execution.recall owner)
              (actualControl.execution.observe nativeApplication owner) canonical)).support,
        ∃ history : (nativeProtocol).History,
          sourceRawReplay setup implementation who target reference
              ⟨some after, prior.extend joint legal moved⟩ (choice :: script) = some history ∧
            TracePrefix actual history.trace ∧
            RawReplayState setup implementation who target reference
              (rawReplayLost setup implementation (choice :: script))
              ⟨some after, prior.extend joint legal moved⟩ history ∧
            mechanicalWord setup implementation who history.trace =
              mechanicalWord setup implementation who (prior.extend joint legal moved) := by
  classical
  let first : (nativeApplication).Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), some ⟨payload, old⟩⟩, evidence⟩⟩
  let oldCanonical := phaseBindingResponse implementation.runtime implementation.leaks owner
    event payload (.success old) serial
  let replacement := phaseBindingResponse implementation.runtime implementation.leaks owner
    event payload (.success next) serial
  have member : first ∈ PhaseCount.onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner (before.execution.recall owner)
        (before.execution.observe nativeApplication owner) := by
    have offered := legal.2 owner
    rw [selected] at offered
    exact offered.2
  have originalCounts := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler prior)
  have actualCounts := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler actual)
  have initialEq : (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) = nativeInitial := PMF.map_comp _ _ _
  have beforeEq : before = ⟨before.remaining, some owner, before.execution⟩ := by
    cases before with
    | mk remaining actor execution =>
        change actor = some owner at acting
        change (⟨remaining, actor, execution⟩ : (nativeApplication).Control) =
          ⟨remaining, some owner, execution⟩
        rw [acting]
  have originalTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler).Trace
          (some ⟨before.remaining, some owner, before.execution⟩) := by
    rw [initialEq, ← beforeEq]
    exact prior
  have slot := PhaseProposal.binding_slot_of_counted_response implementation.runtime
    implementation.leaks implementation.bounds implementation.plan
      (serviceGraph_revealRelaxedOrdered setup .concurrent) (setup.initialLaw.map encodeInputs)
      implementation.horizon implementation.scheduler before.remaining owner before.execution
        originalTrace event payload binding request serial (some ⟨payload, old⟩) evidence
          member allValues
  have oldMember := (Finset.mem_filter.mp slot).2.2 (.success old)
  have same := PhaseProposal.responseClass_binding implementation.runtime implementation.leaks
    implementation.bounds owner (before.execution.recall owner)
      (before.execution.observe nativeApplication owner) event payload binding serial
        (some ⟨payload, old⟩) evidence member (by
          simpa only [Option.bind_some, Raw.as?_mk, Option.elim_some] using oldMember)
  have oldClass : PhaseProposal.projectResponse implementation.runtime implementation.leaks
      implementation.bounds owner (before.execution.recall owner)
        (before.execution.observe nativeApplication owner) ⟨first, member⟩ =
      PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (before.execution.recall owner)
          (before.execution.observe nativeApplication owner) ⟨oldCanonical, oldMember⟩ := by
    apply Subtype.ext
    change PhaseProposal.responseClass implementation.runtime implementation.leaks
      implementation.bounds owner (before.execution.recall owner)
        (before.execution.observe nativeApplication owner) ⟨first, member⟩ =
      PhaseProposal.responseClass implementation.runtime implementation.leaks
        implementation.bounds owner (before.execution.recall owner)
          (before.execution.observe nativeApplication owner) ⟨oldCanonical, oldMember⟩
    simpa only [first, oldCanonical, Option.bind_some, Raw.as?_mk, Option.elim_some] using same
  have oldEffects := proper_response_class_effects setup implementation owner before.execution
    originalCounts ⟨first, member⟩ ⟨oldCanonical, oldMember⟩ _ rfl event
      (owner, .prepared serial) payload binding old rfl (by
        simp only [PhaseProposal.bindingPreparation, binding, Option.bind_some, Raw.as?_mk,
          Option.map_some]) oldClass
  have fresh := PhaseCount.onePacket_binding_fresh implementation.runtime implementation.leaks
    implementation.bounds implementation.plan (setup.initialLaw.map encodeInputs)
      implementation.horizon implementation.scheduler originalTrace owner event serial
        (some ⟨payload, old⟩) evidence member
  have afterEq : after = { before with
      actor := none
      execution := before.execution.respond nativeApplication owner first } := by
    have reached := moved
    change some after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some before) joint).support at reached
    simpa only [ReactiveApplication.transition, acting, selected, Option.getD_some,
      PMF.mem_support_pure_iff, Option.some.injEq] using reached
  have afterResult : after.execution.application.current.native.bindingResult
      (owner, .prepared serial) payload = .success old := by
    rw [afterEq]
    change (before.execution.respond nativeApplication owner
      first).application.current.native.bindingResult
      (owner, .prepared serial) payload = _
    rw [oldEffects.1]
    exact phaseBindingResponse_result implementation.runtime implementation.leaks
      before.execution owner event payload (.success old) serial fresh
  have afterLookup := (State.bindingResult_eq_success_iff after.execution.application.current.native
    (owner, .prepared serial) payload old).mp afterResult
  have stable := phaseApplication_preservesFixedCandidates implementation.runtime
    implementation.leaks
  have invariant : (nativeApplication).Invariant (fun state =>
      state.current.native.candidates.lookup (owner, .prepared serial) =
        .openable (⟨payload, old⟩ : Raw L)) := by
    constructor
    · intro state actor material known
      exact (stable.submit state actor material _ (by rw [known]; simp)).trans known
    · intro state message next known handled
      exact (stable.handle state message next handled _ (by rw [known]; simp)).trans known
    · intro state command next known reached
      exact (stable.environment state command next reached _ (by rw [known]; simp)).trans known
  have registered := invariant.tracePrefix (nativeMenu) nativeInitial implementation.horizon
    implementation.scheduler after reference (prior.extend joint legal moved) referenceTrace
      onward afterLookup
  have newMember : replacement ∈ PhaseCount.onePacketActions implementation.runtime
      implementation.leaks implementation.bounds owner (actualControl.execution.recall owner)
        (actualControl.execution.observe nativeApplication owner) := by
    exact sourceSnapshot_binding_available setup implementation target reference lost
      before.execution actualControl.execution (congrArg (fun c => c.execution.application)
        assigned)
      (congrArg (fun c => c.execution.network) assigned).symm originalCounts actualCounts
      owner event serial (some ⟨payload, old⟩) (some ⟨payload, next⟩) evidence
        (allValues next) member
  let canonical : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (actualControl.execution.recall owner)
        (actualControl.execution.observe nativeApplication owner) := ⟨replacement, newMember⟩
  refine ⟨canonical, rfl, ?_⟩
  intro choice supported
  obtain ⟨response, choiceEq, responseClass⟩ := sourceReplayAliases_support setup implementation
    scale owner actualControl.execution draw _ choice supported
  have scriptLost : rawReplayLost setup implementation (choice :: script) = lost := by
    rw [choiceEq]
    exact lostEq.symm
  have actualEffects := proper_response_class_effects setup implementation owner
    actualControl.execution actualCounts canonical response _ rfl event
      (owner, .prepared serial) payload binding next rfl (by
        simp only [PhaseProposal.bindingPreparation, binding, Option.bind_some, Raw.as?_mk,
          Option.map_some]) responseClass.symm
  have assignedResponse := sourceReplayExecution_proper_respond setup implementation target
    reference lost recalls before.execution owner event payload serial old next registered meaning
  dsimp only at assignedResponse
  have application : (actualControl.execution.respond nativeApplication owner
    response.val).application =
      sourceSnapshotAssignment setup implementation target reference lost
        (before.execution.respond nativeApplication owner first).application := by
    rw [← actualEffects.1]
    change (actualControl.execution.respond nativeApplication owner replacement).application = _
    rw [assigned]
    rw [assignedResponse]
    exact congrArg (sourceSnapshotAssignment setup implementation target reference lost)
      oldEffects.1.symm
  have network : (actualControl.execution.respond nativeApplication owner response.val).network =
      (before.execution.respond nativeApplication owner first).network := by
    rw [← actualEffects.2]
    change (actualControl.execution.respond nativeApplication owner replacement).network = _
    rw [assigned]
    rw [assignedResponse]
    exact oldEffects.2.symm
  exact sourceRawReplay_foreign_extend setup implementation who target reference before after
    referenceTrace prior joint legal moved owner foreign acting first selected script choice lost
      scriptLost recalls actualControl assigned actual replayed past word nextImage response
        (by simp only [choiceEq]) application network

/- A historical never-admitted preparation draws its value before its raw
alias. Freshness makes the actual input independent of that new value. The
resulting normalized law executes every supported pair of draws. -/
private theorem sourceRawReplay_binding_law
    (operational : implementation.Operational)
    (who : Player) (reference before after : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (selectedEvent : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference
      (sourceCutTrace setup implementation referenceTrace) who selectedEvent)
    (g : setup.proposalRecoveryProtocol.History)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (alignment : SourceReplayAlignment (setup := setup) (values := values)
      (implementation := implementation) operational who reference
      referenceTrace selectedEvent cut g sourceChoice targetCurrent targetTrace)
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (onward : TracePrefix (prior.extend joint legal moved) referenceTrace)
    (owner : Player) (foreign : owner ≠ who) (acting : before.actor = some owner)
    (script : List (RawReplayChoice setup implementation))
    (restricted : SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who (rawReplayLost setup implementation script))
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (actualControl : (nativeApplication).Control)
    (assigned : actualControl = { before with
      execution := sourceReplayExecution setup implementation ⟨some targetCurrent, targetTrace⟩
        reference (rawReplayLost setup implementation script) recalls before.execution })
    (actual : (nativeProtocol).Trace (some actualControl))
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
      reference ⟨some before, prior⟩ script = some ⟨some actualControl, actual⟩)
    (past : recalls who = before.execution.recall who)
    (word : mechanicalWord setup implementation who actual =
      mechanicalWord setup implementation who prior)
    (scale : Set.Icc (0 : ℝ) 1)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, event⟩)
    (serial : Nat) (old : L.Val payload)
    (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (selected : joint owner = some
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), some ⟨payload, old⟩⟩, evidence⟩⟩)
    (allValues : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈
      implementation.bounds.values)
    (notDrawn : rawReplayLost setup implementation script (owner, .prepared serial) = none) :
    after.execution.application.current.native.candidates.lookup (owner, .prepared serial) =
        .openable (⟨payload, old⟩ : Raw L) ∧
    ∃ (key : setup.ProposalRecoveryComponent owner)
      (kernel : PMF (RawReplayChoice setup implementation)),
      phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
          implementation.plan owner event (actualControl.execution.recall owner)
            (actualControl.execution.observe nativeApplication owner) = some key ∧
      ((∃ (value : L.Val payload)
          (canonical : PhaseProposal.Response implementation.runtime implementation.leaks
            implementation.bounds owner (actualControl.execution.recall owner)
              (actualControl.execution.observe nativeApplication owner)),
          sourceHandleMeaning setup implementation ⟨some targetCurrent, targetTrace⟩ reference
            (owner, .prepared serial) = some (⟨payload, value⟩ : Raw L) ∧
          canonical.val = phaseBindingResponse implementation.runtime implementation.leaks
            owner event payload (.success value) serial ∧
          kernel = sourceReplayAliases setup implementation scale owner actualControl.execution
            none (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (actualControl.execution.recall owner)
                (actualControl.execution.observe nativeApplication owner) canonical)) ∨
        (sourceHandleMeaning setup implementation ⟨some targetCurrent, targetTrace⟩ reference
            (owner, .prepared serial) = none ∧
          ∃ canonical : ∀ _value : L.Val payload,
              PhaseProposal.Response implementation.runtime implementation.leaks
                implementation.bounds owner (actualControl.execution.recall owner)
                  (actualControl.execution.observe nativeApplication owner),
            (∀ value, (canonical value).val = phaseBindingResponse implementation.runtime
              implementation.leaks owner event payload (.success value) serial) ∧
            kernel = ((values owner key).map (fun choice => phaseRecoveryDomainValue setup
              .concurrent event owner payload binding choice.val.val)).bind (fun value =>
                sourceReplayAliases setup implementation scale owner actualControl.execution
                  (some ((owner, .prepared serial), (⟨payload, value⟩ : Raw L)))
                  (PhaseProposal.projectResponse implementation.runtime implementation.leaks
                    implementation.bounds owner (actualControl.execution.recall owner)
                      (actualControl.execution.observe nativeApplication owner)
                        (canonical value))))) ∧
      SourceReplayCallbackAtoms (setup := setup) (values := values)
        (implementation := implementation) scale owner actualControl.execution
          ⟨some targetCurrent, targetTrace⟩ reference ((joint owner).getD ⟨none⟩) kernel ∧
      ∀ choice ∈ kernel.support,
        SourceReplayLostRestricted setup implementation ⟨some targetCurrent, targetTrace⟩
          reference who (rawReplayLost setup implementation (choice :: script)) ∧
        ∃ history : (nativeProtocol).History,
          sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
              ⟨some after, prior.extend joint legal moved⟩ (choice :: script) = some history ∧
            TracePrefix actual history.trace ∧
            RawReplayState setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
              (rawReplayLost setup implementation (choice :: script))
              ⟨some after, prior.extend joint legal moved⟩ history ∧
            mechanicalWord setup implementation who history.trace =
              mechanicalWord setup implementation who (prior.extend joint legal moved) := by
  classical
  let target : setup.proposalRecoveryProtocol.History := ⟨some targetCurrent, targetTrace⟩
  let lost := rawReplayLost setup implementation script
  let handle : Handle (serviceGraph setup .concurrent) := (owner, .prepared serial)
  let first : (nativeApplication).Action :=
    ⟨some ⟨⟨.commitment event handle, some ⟨payload, old⟩⟩, evidence⟩⟩
  have member : first ∈ PhaseCount.onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner (before.execution.recall owner)
        (before.execution.observe nativeApplication owner) := by
    have offered := legal.2 owner
    rw [selected] at offered
    exact offered.2
  have initialEq : (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) = nativeInitial := PMF.map_comp _ _ _
  have fresh : before.execution.application.current.native.candidates.lookup handle = .fresh := by
    exact PhaseCount.onePacket_binding_fresh implementation.runtime implementation.leaks
      implementation.bounds implementation.plan (setup.initialLaw.map encodeInputs)
        implementation.horizon implementation.scheduler (initialEq.symm ▸ prior) owner event
          serial (some ⟨payload, old⟩) evidence member
  have kept : TracePrefix prior referenceTrace :=
    (TracePrefix.extend (TracePrefix.refl (prefixTrace := prior)) joint legal moved).trans onward
  have image := alignment.images lost restricted before prior kept
  have actualActor : actualControl.actor = some owner := by rw [assigned]; exact acting
  have actualRequest : actualControl.execution.application.SeedRequest owner
      ⟨actualControl.execution.application.attempt, event⟩ := by
    rw [assigned]
    exact request
  obtain ⟨current, queryTrace, _queryKept, _rank, _generation, _saved, _active, query⟩ :=
    image.query actualControl actual owner foreign event payload binding actualActor
      (congrArg (fun c => c.execution.application) assigned)
      (congrArg (fun c => c.execution.network) assigned)
      (congrArg (fun c => c.execution.receipts) assigned)
      (congrArg (fun c => c.execution.environmentRecall) assigned)
      (by rw [assigned]; exact past) actualRequest
  let key := setup.proposalRecoveryQuery owner
    (setup.proposalRecoveryModel.infoOf owner queryTrace)
  have afterEq : after = { before with
      actor := none
      execution := before.execution.respond nativeApplication owner first } := by
    have reached := moved
    change some after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some before) joint).support at reached
    simpa only [ReactiveApplication.transition, acting, selected, Option.getD_some,
      PMF.mem_support_pure_iff, Option.some.injEq] using reached
  let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.commitment event handle, some ⟨payload, old⟩⟩, evidence⟩
  let packet := (nativeApplication).packet
    ((nativeApplication).submit before.execution.application owner material) owner
      (before.execution.network.known owner) material
  let message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)) :=
    ⟨(owner, before.execution.network.nextSerial owner), packet⟩
  let record : (nativeApplication).PlayerEntry :=
    ⟨before.execution.observe nativeApplication owner, first, some message⟩
  have recordedAfter : record ∈ after.execution.recall owner := by
    rw [afterEq]
    simpa only [ReactiveApplication.Execution.respond, first, ↓reduceIte, record,
      message, packet, material, MessageNetwork.submit] using
        (List.mem_append_right (before.execution.recall owner) (List.mem_singleton_self record))
  have recalled := (nativeApplication).reaches_recall_prefix nativeInitial implementation.horizon
    implementation.scheduler ((nativeMenu).reaches_raw nativeInitial implementation.horizon
      implementation.scheduler onward.reachesWithin) after reference rfl rfl owner
  have recorded : record ∈ reference.execution.recall owner := recalled.subset recordedAfter
  have called : message.payload.packet.call = .commitment event handle :=
    phase_emit_call _ owner _ material
  have result := phase_recorded_material_binding_result implementation.runtime implementation.leaks
    (nativeMenu) nativeInitial implementation.horizon implementation.scheduler after
      (prior.extend joint legal moved) owner event payload serial (some ⟨payload, old⟩) evidence
        record recordedAfter rfl (by exact fresh)
  have known : after.execution.application.current.native.bindingResult handle payload =
      .success old := by
    simpa only [Option.bind_some, Raw.as?_mk, Option.elim_some] using result
  refine ⟨(State.bindingResult_eq_success_iff after.execution.application.current.native
    handle payload old).mp known, ?_⟩
  by_cases missing : sourceHandleMeaning setup implementation target reference handle = none
  · have restrictedValue (value : L.Val payload) : SourceReplayLostRestricted setup implementation
        target reference who (Function.update lost handle (some (⟨payload, value⟩ : Raw L))) := by
      rcases alignment.proper lost restricted before prior kept owner handle
        (⟨payload, value⟩ : Raw L) record message event payload old foreign rfl fresh notDrawn
          recorded rfl rfl called binding rfl (by
            simp only [record, first, PhaseProposal.bindingPreparation, binding,
              Option.bind_some, Raw.as?_mk, Option.map_some]) with proper | absent
      · obtain ⟨next, found⟩ := proper
        rw [missing] at found
        cases found
      · exact absent.2.2
    have extension (value : L.Val payload) := sourceRawReplay_proper_extend setup implementation who
      target reference before after referenceTrace prior joint legal moved onward owner foreign
        acting
        script (some (handle, (⟨payload, value⟩ : Raw L)))
        (Function.update lost handle (some (⟨payload, value⟩ : Raw L)))
        (rawReplayLost_register setup implementation script handle _ none).symm recalls
          actualControl
        (by
          rw [assigned]
          unfold sourceReplayExecution
          rw [sourceSnapshotAssignment_extend_lost setup implementation target reference lost
            handle _ before before prior prior TracePrefix.refl fresh])
        actual replayed past word
        (alignment.images _ (restrictedValue value) after (prior.extend joint legal moved) onward)
        scale event payload binding request serial old value evidence selected allValues (by
          change (sourceHandleMeaning setup implementation target reference handle).orElse
            (fun _ => Function.update lost handle (some (⟨payload, value⟩ : Raw L)) handle) = _
          rw [missing, Function.update_self]
          rfl)
    let canonical := fun value => (extension value).choose
    let kernel := ((values owner key).map (fun choice => phaseRecoveryDomainValue setup
      .concurrent event owner payload binding choice.val.val)).bind (fun value =>
        sourceReplayAliases setup implementation scale owner actualControl.execution
          (some (handle, (⟨payload, value⟩ : Raw L)))
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (actualControl.execution.recall owner)
              (actualControl.execution.observe nativeApplication owner) (canonical value)))
    refine ⟨key, kernel, query, Or.inr ⟨missing, canonical,
      (fun value => (extension value).choose_spec.1), rfl⟩,
      sourceReplayDrawAliases_atoms (setup := setup) (values := values)
        (implementation := implementation) scale owner actualControl.execution target reference
          ((joint owner).getD ⟨none⟩) handle event payload binding material
          (by simp only [selected, Option.getD_some]; rfl) rfl
          (by simp [sourceReplayLostSlot, selected, missing, handle]) key query canonical (by
            intro value
            rw [(extension value).choose_spec.1]
            simp only [phaseBindingResponse, Option.bind_some,
              PhaseProposal.bindingPreparation, binding, Raw.as?_mk, Option.map_some]), ?_⟩
    intro choice supported
    obtain ⟨value, _valueSupported, aliasSupported⟩ := (PMF.mem_support_bind_iff ..).mp supported
    obtain ⟨response, choiceEq, _class⟩ := sourceReplayAliases_support setup implementation scale
      owner actualControl.execution (some (handle, (⟨payload, value⟩ : Raw L))) _ choice
        aliasSupported
    have nextLost : rawReplayLost setup implementation (choice :: script) =
        Function.update lost handle (some (⟨payload, value⟩ : Raw L)) := by
      rw [choiceEq]
      exact rawReplayLost_register setup implementation script handle _ _
    refine ⟨nextLost.symm ▸ restrictedValue value, ?_⟩
    exact (extension value).choose_spec.2 choice aliasSupported
  · have proper : ∃ value : L.Val payload,
        sourceHandleMeaning setup implementation target reference handle =
          some (⟨payload, value⟩ : Raw L) := by
      rcases alignment.proper lost restricted before prior kept owner handle
        (⟨payload, old⟩ : Raw L) record message event payload old foreign rfl fresh notDrawn
          recorded rfl rfl called binding rfl (by
            simp only [record, first, PhaseProposal.bindingPreparation, binding,
              Option.bind_some, Raw.as?_mk, Option.map_some]) with proper | absent
      · exact proper
      · exact (missing absent.1).elim
    obtain ⟨value, meaning⟩ := proper
    obtain ⟨canonical, canonicalEq, extension⟩ := sourceRawReplay_proper_extend setup implementation
      who target reference before after referenceTrace prior joint legal moved onward owner foreign
        acting script none lost rfl recalls actualControl assigned actual replayed past word
        (alignment.images lost restricted after (prior.extend joint legal moved) onward)
        scale event payload binding request serial old value evidence selected allValues (by
          change (sourceHandleMeaning setup implementation target reference handle).orElse
            (fun _ => lost handle) = some (⟨payload, value⟩ : Raw L)
          rw [meaning]
          rfl)
    let kernel := sourceReplayAliases setup implementation scale owner actualControl.execution
      none (PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (actualControl.execution.recall owner)
          (actualControl.execution.observe nativeApplication owner) canonical)
    refine ⟨key, kernel, query, Or.inl ⟨value, canonical, meaning, canonicalEq, rfl⟩,
      sourceReplayAliases_atoms (setup := setup) (values := values)
        (implementation := implementation) scale owner actualControl.execution target reference
          ((joint owner).getD ⟨none⟩)
          (by simp [sourceReplayLostSlot, selected, meaning, handle]) canonical (by
            apply response_not_generated_of_preparation setup implementation owner
            rw [canonicalEq]
            simp only [phaseBindingResponse, Option.bind_some,
              PhaseProposal.bindingPreparation, binding, Raw.as?_mk, Option.map_some,
              ne_eq, reduceCtorEq, not_false_eq_true]), ?_⟩
    intro choice supported
    obtain ⟨response, choiceEq, _class⟩ := sourceReplayAliases_support setup implementation scale
      owner actualControl.execution none _ choice supported
    have nextLost : rawReplayLost setup implementation (choice :: script) = lost := by
      rw [choiceEq]
      rfl
    refine ⟨nextLost.symm ▸ restricted, ?_⟩
    exact extension choice supported

/-- A truthful opening uses its surviving accepted handle at the actual
reconstructed input. Raw preparation and certificate syntax remain alias
coordinates; neither can change the authenticated packet or application. -/
private theorem sourceRawReplay_opening_extend
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference before after : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (owner : Player) (foreign : owner ≠ who) (acting : before.actor = some owner)
    (script : List (RawReplayChoice setup implementation))
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (lostEq : lost = rawReplayLost setup implementation script)
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (actualControl : (nativeApplication).Control)
    (assigned : actualControl = { before with
      execution := sourceReplayExecution setup implementation target reference lost recalls
        before.execution })
    (actual : (nativeProtocol).Trace (some actualControl))
    (replayed : sourceRawReplay setup implementation who target reference
      ⟨some before, prior⟩ script = some ⟨some actualControl, actual⟩)
    (past : recalls who = before.execution.recall who)
    (word : mechanicalWord setup implementation who actual =
      mechanicalWord setup implementation who prior)
    (nextImage : SourceReplayImage setup implementation target reference referenceTrace
      lost who after)
    (scale : Set.Icc (0 : ℝ) 1)
    (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup .concurrent).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup .concurrent).layout payload))
    (outputEq : (serviceGraph setup .concurrent).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup .concurrent).layout) outputEq)
        ((serviceGraph setup .concurrent).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup .concurrent) event =
      .resolve owner payload binding checks outputEq codeEq)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, event⟩)
    (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L)
    (preparation : Option (Raw L)) (evidence : EvidenceRequest (serviceGraph setup .concurrent))
    (selected : joint owner = some
      ⟨some ⟨⟨.opening event handle raw, preparation⟩, evidence⟩⟩) :
    ∃ canonical : PhaseProposal.Response implementation.runtime implementation.leaks
        implementation.bounds owner (actualControl.execution.recall owner)
          (actualControl.execution.observe nativeApplication owner),
      canonical.val = PhaseCount.phaseOpeningResponse implementation.runtime implementation.leaks
        event handle raw ∧
      ∀ choice ∈ (sourceReplayAliases setup implementation scale owner actualControl.execution
          none (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (actualControl.execution.recall owner)
              (actualControl.execution.observe nativeApplication owner) canonical)).support,
        ∃ history : (nativeProtocol).History,
          sourceRawReplay setup implementation who target reference
              ⟨some after, prior.extend joint legal moved⟩ (choice :: script) = some history ∧
            TracePrefix actual history.trace ∧
            RawReplayState setup implementation who target reference
              (rawReplayLost setup implementation (choice :: script))
                ⟨some after, prior.extend joint legal moved⟩ history ∧
            mechanicalWord setup implementation who history.trace =
              mechanicalWord setup implementation who (prior.extend joint legal moved) := by
  classical
  let first : (nativeApplication).Action :=
    ⟨some ⟨⟨.opening event handle raw, preparation⟩, evidence⟩⟩
  have member : first ∈ PhaseCount.onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner (before.execution.recall owner)
        (before.execution.observe nativeApplication owner) := by
    have offered := legal.2 owner
    rw [selected] at offered
    exact offered.2
  have originalCounts := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler prior)
  have afterEq : after = { before with
      actor := none
      execution := before.execution.respond nativeApplication owner first } := by
    have reached := moved
    change some after ∈ ((nativeApplication).transition nativeInitial implementation.horizon
      implementation.scheduler (some before) joint).support at reached
    simpa only [ReactiveApplication.transition, acting, selected, Option.getD_some,
      PMF.mem_support_pure_iff, Option.some.injEq] using reached
  have afterApplication : after.execution.application = before.execution.application := by
    rw [afterEq]
    rfl
  let material : WitnessedSubmission (serviceGraph setup .concurrent) :=
    ⟨⟨.opening event handle raw, preparation⟩, evidence⟩
  let packet := (nativeApplication).packet
    ((nativeApplication).submit before.execution.application owner material) owner
      (before.execution.network.known owner) material
  let message : Message Player (CommitAttemptPacket (serviceGraph setup .concurrent)) :=
    ⟨(owner, before.execution.network.nextSerial owner), packet⟩
  have serials := (nativeApplication).serialsBeforeNext_history implementation.scheduler
    nativeInitial implementation.horizon
      ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler prior)
  have found : after.execution.network.lookup message.id = some message := by
    rw [afterEq]
    change (before.execution.network.submit owner packet).2.lookup
      (owner, before.execution.network.nextSerial owner) = some message
    exact serials.lookup_submit owner packet
  have called : message.payload.packet.call = .opening event handle raw :=
    phase_emit_call _ owner _ material
  have permitted : PhaseCount.permits
      ((nativeApplication).outputs (before.execution.recall owner))
        (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
          (before.execution.recall owner)
            (before.execution.observe nativeApplication owner) material) = true := by
    rcases ((PhaseCount.mem_onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner _ _ _).mp member).2 with impossible | ⟨other, named, allowed⟩
    · cases impossible
    · cases Option.some.inj named
      exact allowed
  rw [PhaseCount.localEnvelope_eq_of_recall implementation.runtime implementation.leaks
    before.execution originalCounts.1 originalCounts.2.1 owner material] at permitted
  have authorized : message.payload.packet.tokenValid = true :=
    ((PhaseCount.permits_eq_true_iff _ _).mp permitted).1
  have current : message.payload.attempt = after.execution.application.attempt := by
    rw [afterApplication]
    rfl
  have token : message.payload.tokenValid after.execution.application.attempt = true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true current, authorized⟩
  have allowed : after.execution.application.allows message.payload.packet.call = true := by
    obtain ⟨phase, installed, inside⟩ := request.2.1
    rw [afterApplication, called]
    simp only [PhaseRuntimeState.allows, Option.mem_def.mp installed, Payload.event?,
      decide_eq_true_eq]
    exact inside
  have active : after.execution.application.current.excludedCall message.payload.packet.call =
      false := by
    rw [afterApplication, called]
    change ((serviceGraph setup .concurrent).actor? event).any
      (fun player => decide (player ∈ before.execution.application.current.excluded)) = false
    rw [request.2.2.2.1, Option.any_some]
    exact decide_eq_false request.2.2.2.2
  have gate : (message.payload.tokenValid after.execution.application.attempt &&
      after.execution.application.allows message.payload.packet.call &&
        !after.execution.application.current.excludedCall message.payload.packet.call) = true := by
    rw [token, allowed, active]
    rfl
  have fixed := nextImage.openingFixed message event handle raw found called gate
    (by rw [afterApplication]; exact request.2.2.1)
  rw [afterApplication] at fixed
  have initialEq : (setup.initialLaw.map encodeInputs).map
      (PhaseRuntimeState.initial implementation.plan) = nativeInitial := PMF.map_comp _ _ _
  have prior' : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler).Trace (some before) := by
    rw [initialEq]
    exact prior
  have beforeEq : before = ⟨before.remaining, some owner, before.execution⟩ := by
    cases before with
    | mk remaining actor execution =>
        change actor = some owner at acting
        change (⟨remaining, actor, execution⟩ : (nativeApplication).Control) =
          ⟨remaining, some owner, execution⟩
        rw [acting]
  have activeTrace : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler).Trace
          (some ⟨before.remaining, some owner, before.execution⟩) := by
    rw [← beforeEq]
    exact prior'
  obtain ⟨candidate, value, named, stored, accepted, _verified⟩ :=
    PhaseCount.onePacket_opening_shape implementation.runtime implementation.leaks
      implementation.bounds implementation.plan (serviceGraph_revealRelaxedOrdered setup
        .concurrent)
      (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
      before.remaining owner before.execution activeTrace event payload binding checks outputEq
        codeEq node request _ member
  have handleEq : handle = candidate := (Payload.opening.inj named).2.1
  have rawEq : raw = (⟨payload, value⟩ : Raw L) := (Payload.opening.inj named).2.2
  subst candidate raw
  have unsent := PhaseCount.unsent_of_nonsilent implementation.runtime implementation.leaks
    implementation.bounds implementation.plan (serviceGraph_revealRelaxedOrdered setup .concurrent)
    (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
      before.remaining owner before.execution activeTrace _ request _ member
  have bounded : (⟨payload, value⟩ : Raw L) ∈ implementation.bounds.values := by
    have rawOffered := ((PhaseCount.mem_onePacketActions implementation.runtime implementation.leaks
      implementation.bounds owner _ _ _).mp member).1
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at rawOffered
    exact ((implementation.bounds.submissions_mem _ _).mp rawOffered).1.1.2
  obtain ⟨other, otherAccepted, _owned, _openable, oldMember⟩ :=
    PhaseCount.phaseOpeningResponse_of_history implementation.runtime implementation.leaks
      implementation.bounds implementation.plan (setup.initialLaw.map encodeInputs)
      implementation.horizon implementation.scheduler prior' owner event payload binding checks
        outputEq codeEq node request unsent value stored bounded
  have otherEq : other = handle := Option.some.inj (otherAccepted.symm.trans accepted)
  subst other
  let swap := HiddenSwap.ofPairs
    (sourceSnapshotPairs setup implementation target reference lost
      before.execution.application.current.native)
    (sourceHandlePairs setup implementation target reference lost)
  have fixedFields : swap.values.value binding.field = id ∧
      ∀ candidate, before.execution.application.current.native.accepted binding.field =
        some candidate → swap.raw candidate = id := by
    simpa only [RevealFixed, node] using fixed
  have storeAt : (swap.values.store before.execution.application.current.native.config.store)
      binding.field = before.execution.application.current.native.config.store binding.field := by
    simp only [ValueSwap.store, fixedFields.1, id_eq, Option.map_id]
  have actualStored : binding.get? actualControl.execution.application.current.native.config.store =
      some (.success value) := by
    rw [assigned]
    change binding.get? (before.execution.application.current.native.swap swap).config.store = _
    rw [State.swap_config, Config.swap_store, binding.get?_congr _ _ storeAt]
    exact stored
  have actualCounts := PhaseCount.countRecall_history implementation.runtime implementation.leaks
    ((nativeMenu).toRawTrace nativeInitial implementation.horizon implementation.scheduler actual)
  have outputs : (nativeApplication).outputs (before.execution.recall owner) =
      (nativeApplication).outputs (actualControl.execution.recall owner) := by
    rw [← originalCounts.1 owner, ← actualCounts.1 owner, assigned]
    rfl
  have actualRequest : actualControl.execution.application.SeedRequest owner
      ⟨actualControl.execution.application.attempt, event⟩ := by
    rw [assigned]
    exact request
  have actualUnsent : ∀ message ∈ (nativeApplication).outputs
      (actualControl.execution.recall owner), PhaseCount.event? message.payload ≠
        some ⟨actualControl.execution.application.attempt, event⟩ := by
    rw [← outputs, assigned]
    exact unsent
  have actual' : ((nativeMenu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
        implementation.horizon implementation.scheduler).Trace (some actualControl) := by
    rw [initialEq]
    exact actual
  obtain ⟨other, otherAccepted, _owned, _openable, newMember⟩ :=
    PhaseCount.phaseOpeningResponse_of_history implementation.runtime implementation.leaks
      implementation.bounds implementation.plan (setup.initialLaw.map encodeInputs)
      implementation.horizon implementation.scheduler actual' owner event payload binding checks
        outputEq codeEq node actualRequest actualUnsent value actualStored bounded
  have actualAccepted : actualControl.execution.application.current.native.accepted binding.field =
      some handle := by
    rw [assigned]
    exact accepted
  have otherEq : other = handle := Option.some.inj (otherAccepted.symm.trans actualAccepted)
  subst other
  let replacement := PhaseCount.phaseOpeningResponse implementation.runtime implementation.leaks
    event handle (⟨payload, value⟩ : Raw L)
  have oldClass : PhaseProposal.projectResponse implementation.runtime implementation.leaks
      implementation.bounds owner (before.execution.recall owner)
        (before.execution.observe nativeApplication owner) ⟨first, member⟩ =
      PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (before.execution.recall owner)
          (before.execution.observe nativeApplication owner) ⟨replacement, oldMember⟩ :=
    Subtype.ext (PhaseProposal.responseClass_opening implementation.runtime implementation.leaks
      implementation.bounds owner _ _ event handle _ preparation evidence member oldMember)
  have oldEffects := opening_response_class_effects setup implementation owner before.execution
    originalCounts ⟨first, member⟩ ⟨replacement, oldMember⟩ _ rfl event handle _ rfl oldClass
  let canonical : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (actualControl.execution.recall owner)
        (actualControl.execution.observe nativeApplication owner) := ⟨replacement, newMember⟩
  refine ⟨canonical, rfl, ?_⟩
  intro choice supported
  obtain ⟨response, choiceEq, responseClass⟩ := sourceReplayAliases_support setup implementation
    scale owner actualControl.execution none _ choice supported
  have scriptLost : rawReplayLost setup implementation (choice :: script) = lost := by
    rw [choiceEq]
    exact lostEq.symm
  have actualEffects := opening_response_class_effects setup implementation owner
    actualControl.execution actualCounts canonical response _ rfl event handle _ rfl
      responseClass.symm
  have assignedResponse := sourceReplayExecution_respond setup implementation target reference lost
    recalls before.execution owner replacement (by
      intro material transmitted
      cases Option.some.inj transmitted
      change swap.raw handle (⟨payload, value⟩ : Raw L) = (⟨payload, value⟩ : Raw L)
      rw [fixedFields.2 handle accepted]
      rfl)
  have unchanged : swap.phaseAction replacement = replacement := rfl
  dsimp only at assignedResponse
  rw [unchanged] at assignedResponse
  have application : (actualControl.execution.respond nativeApplication owner
    response.val).application =
      sourceSnapshotAssignment setup implementation target reference lost
        (before.execution.respond nativeApplication owner first).application := by
    rw [← actualEffects.1]
    change (actualControl.execution.respond nativeApplication owner replacement).application = _
    rw [assigned]
    rw [assignedResponse]
    exact congrArg (sourceSnapshotAssignment setup implementation target reference lost)
      oldEffects.1.symm
  have network : (actualControl.execution.respond nativeApplication owner response.val).network =
      (before.execution.respond nativeApplication owner first).network := by
    rw [← actualEffects.2]
    change (actualControl.execution.respond nativeApplication owner replacement).network = _
    rw [assigned]
    rw [assignedResponse]
    exact oldEffects.2.symm
  exact sourceRawReplay_foreign_extend setup implementation who target reference before after
    referenceTrace prior joint legal moved owner foreign acting first selected script choice lost
      scriptLost recalls actualControl assigned actual replayed past word nextImage response
        (by simp only [choiceEq]) application network

/-- A foreign WAIT remains an actual callback slot. It consumes no value
draw and cannot change the focal player's raw recall. -/
private theorem sourceRawReplay_wait_extend
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference before after : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (owner : Player) (foreign : owner ≠ who) (acting : before.actor = some owner)
    (selected : joint owner = some ⟨none⟩)
    (script : List (RawReplayChoice setup implementation))
    (lost : Handle (serviceGraph setup .concurrent) → Option (Raw L))
    (lostEq : lost = rawReplayLost setup implementation script)
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (actualControl : (nativeApplication).Control)
    (assigned : actualControl = { before with
      execution := sourceReplayExecution setup implementation target reference lost recalls
        before.execution })
    (actual : (nativeProtocol).Trace (some actualControl))
    (replayed : sourceRawReplay setup implementation who target reference
      ⟨some before, prior⟩ script = some ⟨some actualControl, actual⟩)
    (past : recalls who = before.execution.recall who)
    (word : mechanicalWord setup implementation who actual =
      mechanicalWord setup implementation who prior)
    (nextImage : SourceReplayImage setup implementation target reference referenceTrace
      lost who after) :
    ∃ history : (nativeProtocol).History,
      sourceRawReplay setup implementation who target reference
          ⟨some after, prior.extend joint legal moved⟩
            ((none, some ⟨none⟩) :: script) = some history ∧
        TracePrefix actual history.trace ∧
        RawReplayState setup implementation who target reference lost
          ⟨some after, prior.extend joint legal moved⟩ history ∧
        mechanicalWord setup implementation who history.trace =
          mechanicalWord setup implementation who (prior.extend joint legal moved) := by
  let response : PhaseProposal.Response implementation.runtime implementation.leaks
      implementation.bounds owner (actualControl.execution.recall owner)
        (actualControl.execution.observe nativeApplication owner) :=
    ⟨⟨none⟩, PhaseCount.silence_onePacket implementation.runtime implementation.leaks
      implementation.bounds owner _ _⟩
  have extendingLost : rawReplayLost setup implementation
      ((none, some ⟨none⟩) :: script) = lost := lostEq.symm
  obtain ⟨history, replay, retained, related, nextWord⟩ := sourceRawReplay_foreign_extend
    setup implementation who target reference before after referenceTrace prior joint legal moved
      owner foreign acting ⟨none⟩ selected script (none, some ⟨none⟩) lost extendingLost recalls
      actualControl assigned actual replayed past word nextImage response rfl
      (congrArg (fun c => c.execution.application) assigned)
      (congrArg (fun c => c.execution.network) assigned)
  rw [extendingLost] at related
  exact ⟨history, replay, retained, related, nextWord⟩

/-- The literal normalized foreign callback is either its actual alias law or
its actual-query value law followed by aliases at that same input. -/
def SourceReplayCallbackLaw
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (kernel : PMF (RawReplayChoice setup implementation)) : Prop :=
  ((∃ canonical : PhaseProposal.Response implementation.runtime implementation.leaks
    implementation.bounds owner (execution.recall owner)
      (execution.observe nativeApplication owner),
    kernel = sourceReplayAliases setup implementation scale owner execution
      none (PhaseProposal.projectResponse implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner) canonical) ∧
    (canonical.val = ⟨none⟩ ∨
      (∃ (event : (serviceGraph setup .concurrent).EventId)
          (handle : Handle (serviceGraph setup .concurrent)) (raw : Raw L),
        canonical.val = PhaseCount.phaseOpeningResponse implementation.runtime
          implementation.leaks event handle raw) ∨
      ∃ (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
          (serial : Nat) (value : L.Val payload),
        (serviceGraph setup .concurrent).outputLayout event = .binding owner payload ∧
        sourceHandleMeaning setup implementation target reference (owner, .prepared serial) =
          some (⟨payload, value⟩ : Raw L) ∧
        canonical.val = phaseBindingResponse implementation.runtime implementation.leaks
          owner event payload (.success value) serial)) ∨
  ∃ (event : (serviceGraph setup .concurrent).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup .concurrent).outputLayout event = .binding owner payload)
    (key : setup.ProposalRecoveryComponent owner) (serial : Nat)
    (canonical : ∀ _value : L.Val payload,
      PhaseProposal.Response implementation.runtime implementation.leaks
        implementation.bounds owner (execution.recall owner)
          (execution.observe nativeApplication owner)),
    phaseProposalQuery? setup .concurrent implementation.runtime implementation.leaks
        implementation.plan owner event (execution.recall owner)
          (execution.observe nativeApplication owner) = some key ∧
    sourceHandleMeaning setup implementation target reference
      (owner, .prepared serial) = none ∧
    (∀ value, (canonical value).val = phaseBindingResponse implementation.runtime
      implementation.leaks owner event payload (.success value) serial) ∧
    kernel = ((values owner key).map (fun sampled => phaseRecoveryDomainValue setup
      .concurrent event owner payload binding sampled.val.val)).bind (fun value =>
        sourceReplayAliases setup implementation scale owner execution
          (some ((owner, .prepared serial), (⟨payload, value⟩ : Raw L)))
          (PhaseProposal.projectResponse implementation.runtime implementation.leaks
            implementation.bounds owner (execution.recall owner)
              (execution.observe nativeApplication owner) (canonical value))))

/- Every factual foreign callback has a normalized actual response kernel.
The emitted packet class is retained, while only a fresh historical lost
preparation receives an auxiliary value coordinate. -/
theorem sourceRawReplay_foreign_law
    (operational : implementation.Operational)
    (who : Player) (reference before after : (nativeApplication).Control)
    (referenceTrace : (nativeProtocol).Trace (some reference))
    (selectedEvent : (serviceGraph setup .concurrent).EventId)
    (cut : PhaseProposalCanonicalBindingCut setup .concurrent implementation.runtime
      implementation.leaks implementation.bounds implementation.plan values
      implementation.horizon implementation.scheduler reference
      (sourceCutTrace setup implementation referenceTrace) who selectedEvent)
    (g : setup.proposalRecoveryProtocol.History)
    (sourceChoice : setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who g.trace))
    (targetCurrent : CommitRecoveryState setup.program)
    (targetTrace : setup.proposalRecoveryProtocol.Trace (some targetCurrent))
    (alignment : SourceReplayAlignment (setup := setup) (values := values)
      (implementation := implementation) operational who reference
      referenceTrace selectedEvent cut g sourceChoice targetCurrent targetTrace)
    (prior : (nativeProtocol).Trace (some before))
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal (some before) joint)
    (moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support)
    (onward : TracePrefix (prior.extend joint legal moved) referenceTrace)
    (owner : Player) (foreign : owner ≠ who) (acting : before.actor = some owner)
    (good : ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime
      implementation.leaks implementation.bounds nativeInitial implementation.horizon
        implementation.scheduler owner ⟨some reference, referenceTrace⟩)
    (script : List (RawReplayChoice setup implementation))
    (restricted : SourceReplayLostRestricted setup implementation
      ⟨some targetCurrent, targetTrace⟩ reference who (rawReplayLost setup implementation script))
    (introduced : ∀ handle raw, rawReplayLost setup implementation script handle = some raw →
      before.execution.application.current.native.candidates.lookup handle ≠ .fresh)
    (recalls : Player → List (nativeApplication).PlayerEntry)
    (actualControl : (nativeApplication).Control)
    (assigned : actualControl = { before with
      execution := sourceReplayExecution setup implementation ⟨some targetCurrent, targetTrace⟩
        reference (rawReplayLost setup implementation script) recalls before.execution })
    (actual : (nativeProtocol).Trace (some actualControl))
    (replayed : sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩
      reference ⟨some before, prior⟩ script = some ⟨some actualControl, actual⟩)
    (past : recalls who = before.execution.recall who)
    (word : mechanicalWord setup implementation who actual =
      mechanicalWord setup implementation who prior)
    (scale : Set.Icc (0 : ℝ) 1) :
    ∃ kernel : PMF (RawReplayChoice setup implementation),
      SourceReplayCallbackAtoms (setup := setup) (values := values)
        (implementation := implementation) scale owner actualControl.execution
          ⟨some targetCurrent, targetTrace⟩ reference ((joint owner).getD ⟨none⟩) kernel ∧
      SourceReplayCallbackLaw (setup := setup) (values := values)
        (implementation := implementation) scale owner actualControl.execution
          ⟨some targetCurrent, targetTrace⟩ reference kernel ∧
      ∀ choice ∈ kernel.support,
        SourceReplayLostRestricted setup implementation ⟨some targetCurrent, targetTrace⟩
          reference who (rawReplayLost setup implementation (choice :: script)) ∧
        (∀ handle raw, rawReplayLost setup implementation (choice :: script) handle = some raw →
          after.execution.application.current.native.candidates.lookup handle ≠ .fresh) ∧
        ∃ history : (nativeProtocol).History,
          sourceRawReplay setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
              ⟨some after, prior.extend joint legal moved⟩ (choice :: script) = some history ∧
            TracePrefix actual history.trace ∧
            RawReplayState setup implementation who ⟨some targetCurrent, targetTrace⟩ reference
              (rawReplayLost setup implementation (choice :: script))
              ⟨some after, prior.extend joint legal moved⟩ history ∧
            mechanicalWord setup implementation who history.trace =
              mechanicalWord setup implementation who (prior.extend joint legal moved) := by
  classical
  let target : setup.proposalRecoveryProtocol.History := ⟨some targetCurrent, targetTrace⟩
  let lost := rawReplayLost setup implementation script
  have kept : TracePrefix prior referenceTrace :=
    (TracePrefix.extend (TracePrefix.refl (prefixTrace := prior)) joint legal moved).trans onward
  have nextImage := alignment.images lost restricted after (prior.extend joint legal moved) onward
  have carry (handle : Handle (serviceGraph setup .concurrent))
      (fixed : before.execution.application.current.native.candidates.lookup handle ≠ .fresh) :
      after.execution.application.current.native.candidates.lookup handle ≠ .fresh := by
    let stable := phaseApplication_preservesFixedCandidates implementation.runtime
      implementation.leaks
    have invariant : (nativeApplication).Invariant (fun state =>
        state.current.native.candidates.lookup handle =
          before.execution.application.current.native.candidates.lookup handle) := by
      constructor
      · intro state actor material known
        exact (stable.submit state actor material handle (by rw [known]; exact fixed)).trans known
      · intro state message next known handled
        exact (stable.handle state message next handled handle (by rw [known]; exact
          fixed)).trans known
      · intro state command next known reached
        exact (stable.environment state command next reached handle
          (by rw [known]; exact fixed)).trans known
    rw [invariant.tracePrefix (nativeMenu) nativeInitial implementation.horizon
      implementation.scheduler before after prior (prior.extend joint legal moved)
        (TracePrefix.extend (TracePrefix.refl (prefixTrace := prior)) joint legal moved) rfl]
    exact fixed
  obtain ⟨first, selected, member⟩ : ∃ first : (nativeApplication).Action,
      joint owner = some first ∧ first ∈ PhaseCount.onePacketActions implementation.runtime
        implementation.leaks implementation.bounds owner (before.execution.recall owner)
          (before.execution.observe nativeApplication owner) := by
    have offered := legal.2 owner
    cases chosen : joint owner with
    | none => rw [chosen] at offered; exact (offered (by exact acting)).elim
    | some action => exact ⟨action, rfl, (chosen ▸ offered).2⟩
  cases first with
  | mk transmission =>
    cases transmission with
    | none =>
      let canonical : PhaseProposal.Response implementation.runtime implementation.leaks
          implementation.bounds owner (actualControl.execution.recall owner)
            (actualControl.execution.observe nativeApplication owner) :=
        ⟨⟨none⟩, PhaseCount.silence_onePacket implementation.runtime implementation.leaks
          implementation.bounds owner _ _⟩
      refine ⟨sourceReplayAliases setup implementation scale owner actualControl.execution none
        (PhaseProposal.projectResponse implementation.runtime implementation.leaks
          implementation.bounds owner (actualControl.execution.recall owner)
            (actualControl.execution.observe nativeApplication owner) canonical),
        sourceReplayAliases_atoms (setup := setup) (values := values)
          (implementation := implementation) scale owner actualControl.execution target reference
            ((joint owner).getD ⟨none⟩) (by simp [sourceReplayLostSlot, selected]) canonical (by
              rintro ⟨otherEvent, otherPayload, serial, opening, evidence, _layout, action,
                _missing⟩
              have absent := congrArg
                (fun response : (nativeApplication).Action => response.transmission) action
              change none = some _ at absent
              cases absent), Or.inl ⟨canonical, rfl, Or.inl rfl⟩, ?_⟩
      intro choice supported
      obtain ⟨response, choiceEq, responseClass⟩ := sourceReplayAliases_support setup implementation
        scale owner actualControl.execution none _ choice supported
      have actionEq : response.val = (⟨none⟩ : (nativeApplication).Action) := by
        have packetEq := congrArg (fun chosen => chosen.val.2) responseClass
        change response.val.transmission.map _ = none at packetEq
        cases response with
        | mk action legalResponse =>
          cases action with
          | mk sent => cases sent <;> simp_all only [Option.map_none, Option.map_some, reduceCtorEq]
      rw [actionEq] at choiceEq
      cases choiceEq
      obtain ⟨history, replay, retained, related, nextWord⟩ := sourceRawReplay_wait_extend
        setup implementation who target reference before after referenceTrace prior joint legal
          moved owner foreign acting selected script lost rfl recalls actualControl assigned actual
            replayed past word nextImage
      refine ⟨restricted, ?_, history, replay, retained, related, nextWord⟩
      intro handle raw drawn
      exact carry handle (introduced handle raw drawn)
    | some material =>
      have initialEq : (setup.initialLaw.map encodeInputs).map
          (PhaseRuntimeState.initial implementation.plan) = nativeInitial := PMF.map_comp _ _ _
      have beforeEq : before = ⟨before.remaining, some owner, before.execution⟩ := by
        cases before with
        | mk remaining actor execution =>
          change actor = some owner at acting
          change (⟨remaining, actor, execution⟩ : (nativeApplication).Control) =
            ⟨remaining, some owner, execution⟩
          rw [acting]
      have originalTrace : ((nativeMenu).protocol
          ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial implementation.plan))
            implementation.horizon implementation.scheduler).Trace
              (some ⟨before.remaining, some owner, before.execution⟩) := by
        rw [initialEq, ← beforeEq]
        exact prior
      obtain ⟨coordinate, request⟩ := PhaseCount.onePacket_request_of_nonsilent
        implementation.runtime
        implementation.leaks implementation.bounds implementation.plan (setup.initialLaw.map
          encodeInputs)
          implementation.horizon implementation.scheduler before.remaining owner before.execution
            originalTrace material member
      have named := PhaseCount.onePacket_event_of_request implementation.runtime
        implementation.leaks
        implementation.bounds implementation.plan (serviceGraph_revealRelaxedOrdered setup
          .concurrent)
          (setup.initialLaw.map encodeInputs) implementation.horizon implementation.scheduler
            before.remaining owner before.execution originalTrace coordinate request material member
      have allowed : PhaseCount.permits ((nativeApplication).outputs (before.execution.recall
        owner))
          (PhaseCount.localEnvelope implementation.runtime implementation.leaks owner
            (before.execution.recall owner) (before.execution.observe nativeApplication owner)
              material) = true := by
        rcases ((PhaseCount.mem_onePacketActions implementation.runtime implementation.leaks
          implementation.bounds owner _ _ _).mp member).2 with impossible | ⟨other, equal, allowed⟩
        · cases impossible
        · cases Option.some.inj equal
          exact allowed
      have correct := ((PhaseCount.permits_eq_true_iff _ _).mp allowed).2.1
      have actualCall : (PhaseCount.nativeMessage (PhaseCount.localEnvelope implementation.runtime
          implementation.leaks owner (before.execution.recall owner)
            (before.execution.observe nativeApplication owner) material)).payload.call =
          material.call.packet := PhaseCount.maskPacket_call _ _
      unfold CountCallCorrect at correct
      rw [actualCall] at correct
      rcases material with ⟨⟨packet, preparation⟩, evidence⟩
      cases packet with
      | malformed raw => cases correct
      | commitment event handle =>
        obtain ⟨bindingOwned, _, handleOwned, ⟨serial, slot⟩, _⟩ := correct
        change handle.1 = owner at handleOwned
        have handleEq : handle = (owner, .prepared serial) := Prod.ext handleOwned slot
        subst handle
        have eventEq : coordinate.event = event := Option.some.inj named.symm
        have requestEvent := request
        change before.execution.application.SeedRequest owner ⟨coordinate.attempt, coordinate.event⟩
          at requestEvent
        rw [request.1, eventEq] at requestEvent
        cases node : nodeView (serviceGraph setup .concurrent) event with
        | sample payload law outputEq codeEq =>
          simp only [bindingOwnedBy, outputEq] at bindingOwned
          cases bindingOwned
        | resolve actor payload binding checks outputEq codeEq =>
          simp only [bindingOwnedBy, outputEq] at bindingOwned
          cases bindingOwned
        | bind actor payload binding codeEq =>
          have actorEq : actor = owner := by
            simpa only [bindingOwnedBy, binding, decide_eq_true_eq, PhaseCount.nativeMessage,
              PhaseCount.localEnvelope, Message.sender] using bindingOwned
          subst actor
          have proper : ∃ old : L.Val payload,
              preparation = some (⟨payload, old⟩ : Raw L) := by
            have usable : preparation.bind (fun raw => raw.as? payload) ≠ none := by
              intro unusable
              apply good
              let record := (((nativeMenu).information nativeInitial implementation.horizon
                implementation.scheduler).infoOf owner prior,
                  (⟨some ⟨⟨.commitment event (owner, .prepared serial), preparation⟩, evidence⟩⟩ :
                    (nativeApplication).Action))
              have atStep : record ∈ ((nativeMenu).information nativeInitial implementation.horizon
                  implementation.scheduler).ownPlay owner (prior.extend joint legal moved) := by
                rw [InfoSignals.ownPlay_extend, selected]
                exact List.mem_cons_self
              have atFinal := (((nativeMenu).information nativeInitial implementation.horizon
                implementation.scheduler).ownPlay_isSuffix_of_reachesWithin owner
                  onward.reachesWithin).subset atStep
              exact ⟨record, atFinal, event, payload, serial, preparation, evidence,
                binding, rfl, unusable⟩
            obtain ⟨old, decoded⟩ := Option.ne_none_iff_exists'.mp usable
            obtain ⟨raw, chosen, typed⟩ := Option.bind_eq_some_iff.mp decoded
            have rawEq : raw = (⟨payload, old⟩ : Raw L) := by
              rcases raw with ⟨ty, value⟩
              unfold Raw.as? at typed
              split at typed
              next same =>
                change ty = payload at same
                subst ty
                cases Option.some.inj typed
                rfl
              next different => cases typed
            exact ⟨old, chosen.trans (congrArg some rawEq)⟩
          obtain ⟨old, rfl⟩ := proper
          have fresh := PhaseCount.onePacket_binding_fresh implementation.runtime
            implementation.leaks
            implementation.bounds implementation.plan (setup.initialLaw.map encodeInputs)
              implementation.horizon implementation.scheduler originalTrace owner event serial
                (some ⟨payload, old⟩) evidence member
          have notDrawn : lost (owner, .prepared serial) = none := by
            cases drawn : lost (owner, .prepared serial) with
            | none => rfl
            | some raw => exact (introduced _ raw drawn fresh).elim
          have allValues : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈
              implementation.bounds.values := by
            have covered := operational.outputValues event
            rw [binding] at covered
            exact covered
          obtain ⟨registered, key, kernel, query, description, kernelAtoms, produced⟩ :=
            sourceRawReplay_binding_law (setup := setup) (values := values)
              (implementation := implementation) operational who reference before
              after referenceTrace selectedEvent cut g sourceChoice targetCurrent targetTrace
                alignment
                prior joint legal moved onward owner foreign acting script restricted recalls
                  actualControl assigned actual replayed past word scale event payload binding
                    requestEvent serial old evidence selected allValues notDrawn
          refine ⟨kernel, kernelAtoms, ?_, ?_⟩
          · rcases description with ⟨value, canonical, meaning, canonicalEq, kernelEq⟩ |
              ⟨missing, canonical, canonicalEq, kernelEq⟩
            · exact Or.inl ⟨canonical, kernelEq,
                Or.inr (Or.inr ⟨event, payload, serial, value, binding, meaning, canonicalEq⟩)⟩
            · exact Or.inr ⟨event, payload, binding, key, serial, canonical, query, missing,
                canonicalEq, kernelEq⟩
          · intro choice supported
            obtain ⟨restrictedNext, history, replay, retained, related, nextWord⟩ := produced
              choice supported
            refine ⟨restrictedNext, ?_, history, replay, retained, related, nextWord⟩
            intro handle raw drawn
            rcases description with ⟨value, canonical, _meaning, _canonicalEq, kernelEq⟩ |
              ⟨_missing, canonical, _canonicalEq, kernelEq⟩
            · rw [kernelEq] at supported
              obtain ⟨response, choiceEq, _class⟩ := sourceReplayAliases_support setup
                implementation scale owner actualControl.execution none _ choice supported
              rw [choiceEq] at drawn
              exact carry handle (introduced handle raw drawn)
            · rw [kernelEq] at supported
              obtain ⟨value, _valueSupported, supported⟩ :=
                (PMF.mem_support_bind_iff ..).mp supported
              obtain ⟨response, choiceEq, _class⟩ := sourceReplayAliases_support setup
                implementation scale owner actualControl.execution (some ((owner, .prepared serial),
                  (⟨payload, value⟩ : Raw L))) _ choice supported
              rw [choiceEq, rawReplayLost_register] at drawn
              by_cases same : handle = (owner, .prepared serial)
              · rw [same, registered]
                intro impossible
                cases impossible
              · rw [Function.update_of_ne same] at drawn
                exact carry handle (introduced handle raw drawn)
      | opening event handle raw =>
        have eventEq : coordinate.event = event := Option.some.inj named.symm
        have requestEvent := request
        change before.execution.application.SeedRequest owner ⟨coordinate.attempt, coordinate.event⟩
          at requestEvent
        rw [request.1, eventEq] at requestEvent
        cases node : nodeView (serviceGraph setup .concurrent) event with
        | bind actor payload outputEq codeEq => simp only [node, and_false] at correct
        | sample payload law outputEq codeEq => simp only [node, and_false] at correct
        | resolve actor payload binding checks outputEq codeEq =>
          simp only [node] at correct
          have actorEq : actor = owner := correct.2.1.symm
          subst actor
          obtain ⟨canonical, canonicalEq, produced⟩ := sourceRawReplay_opening_extend
            setup implementation who target reference before after referenceTrace prior joint legal
              moved owner foreign acting script lost rfl recalls actualControl assigned actual
                replayed past word nextImage scale event payload binding checks outputEq codeEq
                  node requestEvent handle raw preparation evidence selected
          refine ⟨sourceReplayAliases setup implementation scale owner actualControl.execution none
            (PhaseProposal.projectResponse implementation.runtime implementation.leaks
              implementation.bounds owner (actualControl.execution.recall owner)
                (actualControl.execution.observe nativeApplication owner) canonical),
            sourceReplayAliases_atoms (setup := setup) (values := values)
              (implementation := implementation) scale owner actualControl.execution target
                reference
                ((joint owner).getD ⟨none⟩) (by simp [sourceReplayLostSlot, selected])
                canonical (by
                  rintro ⟨otherEvent, otherPayload, serial, opening, evidence, _layout, action,
                    _missing⟩
                  have wire := congrArg (fun response : (nativeApplication).Action =>
                    response.transmission.map (fun material => material.call.packet)) action
                  rw [canonicalEq] at wire
                  simp only [PhaseCount.phaseOpeningResponse, Option.map_some] at wire
                  cases wire), Or.inl ⟨canonical, rfl,
                    Or.inr (Or.inl ⟨event, handle, raw, canonicalEq⟩)⟩, ?_⟩
          intro choice supported
          obtain ⟨response, choiceEq, _class⟩ := sourceReplayAliases_support setup implementation
            scale owner actualControl.execution none _ choice supported
          have nextLost : rawReplayLost setup implementation (choice :: script) = lost := by
            rw [choiceEq]
            rfl
          refine ⟨nextLost.symm ▸ restricted, ?_, produced choice supported⟩
          intro handle raw drawn
          rw [nextLost] at drawn
          exact carry handle (introduced handle raw drawn)

inductive SourceReplayScriptMass
    (scale : Set.Icc (0 : ℝ) 1)
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) :
    (nativeProtocol).History → List (RawReplayChoice setup implementation) → ℝ≥0∞ → Prop
  | start : SourceReplayScriptMass scale who target reference
      ⟨(nativeProtocol).init, Trace.start⟩ [] 1
  | deterministic {before after : (nativeProtocol).State}
      {prior : (nativeProtocol).Trace before}
      {joint : Player → Option (nativeApplication).Action}
      {legal : (nativeProtocol).Legal before joint}
      {moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support}
      {script : List (RawReplayChoice setup implementation)} {mass : ℝ≥0∞}
      (quiet : (nativeApplication).actor before = none ∨
        (nativeApplication).actor before = some who)
      (earlier : SourceReplayScriptMass scale who target reference ⟨before, prior⟩ script mass) :
      SourceReplayScriptMass scale who target reference
        ⟨after, prior.extend joint legal moved⟩ ((none, none) :: script) mass
  | foreign {before after : (nativeApplication).Control}
      {prior : (nativeProtocol).Trace (some before)}
      {joint : Player → Option (nativeApplication).Action}
      {legal : (nativeProtocol).Legal (some before) joint}
      {moved : some after ∈ ((nativeProtocol).step (some before) ⟨joint, legal⟩).support}
      {script : List (RawReplayChoice setup implementation)} {mass : ℝ≥0∞}
      (owner : Player) (different : owner ≠ who) (acting : before.actor = some owner)
      (actual : (nativeApplication).Control)
      (actualTrace : (nativeProtocol).Trace (some actual))
      (replayed : sourceRawReplay setup implementation who target reference ⟨some before, prior⟩
        script = some ⟨some actual, actualTrace⟩)
      (related : RawReplayState setup implementation who target reference
        (rawReplayLost setup implementation script) ⟨some before, prior⟩
          ⟨some actual, actualTrace⟩)
      (kernel : PMF (RawReplayChoice setup implementation))
      (atoms : SourceReplayCallbackAtoms (setup := setup) (values := values)
        (implementation := implementation) scale owner actual.execution target reference
          ((joint owner).getD ⟨none⟩) kernel)
      (description : SourceReplayCallbackLaw (setup := setup) (values := values)
        (implementation := implementation) scale owner actual.execution target reference kernel)
      (choice : RawReplayChoice setup implementation) (supported : choice ∈ kernel.support)
      (earlier : SourceReplayScriptMass scale who target reference ⟨some before, prior⟩ script
        mass) :
      SourceReplayScriptMass scale who target reference
        ⟨some after, prior.extend joint legal moved⟩ (choice :: script) (mass * kernel choice)

/-- A normalized sequential script law, together with its actual replay at
every supported script. No native transition or behavioral support is assumed
for an output history. -/
structure SourceRawReplayLaw
    (scale : Set.Icc (0 : ℝ) 1)
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    (original : (nativeProtocol).History) where
  choices : PMF (List (RawReplayChoice setup implementation))
  restricted : ∀ script ∈ choices.support,
    SourceReplayLostRestricted setup implementation target reference who
      (rawReplayLost setup implementation script)
  introduced : ∀ script ∈ choices.support,
    ∀ (control : (nativeApplication).Control), original.state = some control →
      ∀ handle raw, rawReplayLost setup implementation script handle = some raw →
        control.execution.application.current.native.candidates.lookup handle ≠ .fresh
  atoms : ∀ script ∈ choices.support,
    SourceReplayScriptMass (setup := setup) (values := values) (implementation := implementation)
      scale who target reference original script (choices script)
  replayed : ∀ script ∈ choices.support, ∃ actual : (nativeProtocol).History,
    sourceRawReplay setup implementation who target reference original script = some actual ∧
      RawReplayState setup implementation who target reference
        (rawReplayLost setup implementation script) original actual ∧
      mechanicalWord setup implementation who actual.trace =
        mechanicalWord setup implementation who original.trace ∧
      ∀ owner, owner ≠ who →
        ¬ PhaseProposal.GeneratedUnusableBindingHistory implementation.runtime implementation.leaks
          implementation.bounds nativeInitial implementation.horizon implementation.scheduler
            owner actual

def sourceReplayLastAction
    (owner : Player) (actual : (nativeProtocol).History) : Option (nativeApplication).Action :=
  actual.state.bind fun current =>
    (current.execution.recall owner).getLast?.map fun record => record.action

open Classical in
/-- Read every literal callback choice from the replayed raw recall, retaining
one padding coordinate at every other original trace transition. -/
def sourceRawReplayReadback
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) :
    (nativeProtocol).History → (nativeProtocol).History →
      Option (List (RawReplayChoice setup implementation))
  | ⟨_, .start⟩, _ => some []
  | ⟨_, .extend prior joint _ _⟩, actual =>
      (sourceRawReplayReadback who target reference ⟨_, prior⟩ actual.prior).bind fun script =>
        match (nativeApplication).actor (⟨_, prior⟩ : (nativeProtocol).History).state with
        | none => some ((none, none) :: script)
        | some owner =>
            if owner = who then some ((none, none) :: script)
            else (sourceReplayLastAction setup implementation owner actual).map fun action =>
              ((sourceReplayLostSlot setup implementation target reference
                ((joint owner).getD ⟨none⟩)).bind (fun handle =>
                  (action.transmission.bind PhaseProposal.bindingPreparation).map
                    (fun raw => (handle, raw))), some action) :: script

private theorem sourceReplayAppend_prior_state
    (previous actual : (nativeProtocol).History) (next : (nativeProtocol).State)
    (joint : Player → Option (nativeApplication).Action)
    (appended : sourceReplayAppend setup implementation previous next joint = some actual) :
    actual.prior = previous ∧ actual.state = next := by
  classical
  unfold sourceReplayAppend at appended
  split at appended
  · split at appended
    · cases Option.some.inj appended
      exact ⟨rfl, rfl⟩
    · cases appended
  · cases appended

theorem sourceRawReplay_step_prior
    (who : Player) (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control)
    {before after : (nativeProtocol).State} (prior : (nativeProtocol).Trace before)
    (joint : Player → Option (nativeApplication).Action)
    (legal : (nativeProtocol).Legal before joint)
    (moved : after ∈ ((nativeProtocol).step before ⟨joint, legal⟩).support)
    (choice : RawReplayChoice setup implementation)
    (script : List (RawReplayChoice setup implementation))
    (actual : (nativeProtocol).History)
    (replayed : sourceRawReplay setup implementation who target reference
      ⟨after, prior.extend joint legal moved⟩ (choice :: script) = some actual) :
    ∃ previous : (nativeProtocol).History,
      sourceRawReplay setup implementation who target reference ⟨before, prior⟩ script =
        some previous ∧ actual.prior = previous := by
  classical
  rw [sourceRawReplay] at replayed
  obtain ⟨previous, earlier, step⟩ := Option.bind_eq_some_iff.mp replayed
  refine ⟨previous, earlier, ?_⟩
  have appended (next : (nativeProtocol).State)
      (chosen : Player → Option (nativeApplication).Action)
      (h : sourceReplayAppend setup implementation previous next chosen = some actual) :
      actual.prior = previous :=
    (sourceReplayAppend_prior_state setup implementation previous actual next chosen h).1
  cases before with
  | none =>
    cases targetState : target.state with
    | none => simp only [targetState] at step; cases step
    | some current =>
      simp only [targetState] at step
      exact appended _ _ step
  | some original =>
    cases acting : original.actor with
    | none =>
      simp only [acting] at step
      cases actualState : previous.state <;> cases after <;>
        simp only [actualState] at step
      · cases step
      · cases step
      · cases step
      · exact appended _ _ step
    | some owner =>
      simp only [acting] at step
      cases actualState : previous.state with
      | none => simp only [actualState] at step; cases step
      | some current =>
        simp only [actualState] at step
        obtain ⟨action, _selected, produced⟩ := Option.bind_eq_some_iff.mp step
        exact appended _ _ produced

private theorem sourceReplayCallbackAtoms_readback
    (scale : Set.Icc (0 : ℝ) 1) (owner : Player)
    (execution : (nativeApplication).Execution)
    (target : setup.proposalRecoveryProtocol.History)
    (reference : (nativeApplication).Control) (original : (nativeApplication).Action)
    (kernel : PMF (RawReplayChoice setup implementation))
    (atoms : SourceReplayCallbackAtoms (setup := setup) (values := values)
      (implementation := implementation) scale owner execution target reference original kernel)
    (choice : RawReplayChoice setup implementation) (supported : choice ∈ kernel.support) :
    ∃ action : (nativeApplication).Action, choice.2 = some action ∧
      ((sourceReplayLostSlot setup implementation target reference original).bind fun handle =>
        (action.transmission.bind PhaseProposal.bindingPreparation).map fun raw =>
          (handle, raw)) = choice.1 := by
  obtain ⟨tag, response, responseEq, _proper, aliases | lost⟩ := atoms choice supported
  · refine ⟨response.val, responseEq, ?_⟩
    rw [← tag, aliases.1]
    rfl
  · obtain ⟨event, payload, binding, key, handle, value, _original, _query, drawn, prepared,
        _mass⟩ := lost
    refine ⟨response.val, responseEq, ?_⟩
    rw [← tag, drawn, prepared]
    rfl

theorem sourceReplayLastAction_respond
    (owner : Player) (before : (nativeApplication).Control)
    (action : (nativeApplication).Action) (actual : (nativeProtocol).History)
    (state : actual.state = some (⟨before.remaining, none,
      before.execution.respond nativeApplication owner action⟩ : (nativeApplication).Control)) :
    sourceReplayLastAction setup implementation owner actual = some action := by
  unfold sourceReplayLastAction
  rw [state]
  cases action with
  | mk transmission =>
    cases transmission <;>
      simp only [Option.bind_some, ReactiveApplication.Execution.respond, ↓reduceIte,
        List.getLast?_concat, Option.map_some]

/-- Literal script readback is a left inverse on the actual sequential script
mass construction, with every original slot retained. -/
theorem sourceRawReplay_readback
    (scale : Set.Icc (0 : ℝ) 1) (who : Player)
    (target : setup.proposalRecoveryProtocol.History) (reference : (nativeApplication).Control)
    (original : (nativeProtocol).History) (script : List (RawReplayChoice setup implementation))
    (mass : ℝ≥0∞)
    (supported : SourceReplayScriptMass (setup := setup) (values := values)
      (implementation := implementation) scale who target reference original script mass)
    (actual : (nativeProtocol).History)
    (replayed : sourceRawReplay setup implementation who target reference original script =
      some actual) :
    sourceRawReplayReadback setup implementation who target reference original actual =
      some script := by
  classical
  induction supported generalizing actual with
  | start =>
    simp only [sourceRawReplayReadback]
  | @deterministic before after prior joint legal moved script mass quiet earlier ih =>
    obtain ⟨previous, previousReplay, priorEq⟩ := sourceRawReplay_step_prior setup implementation
      who target reference prior joint legal moved (none, none) script actual replayed
    have previousRead := ih previous previousReplay
    rw [sourceRawReplayReadback, priorEq, previousRead, Option.bind_some]
    rcases quiet with quiet | quiet <;> simp only [quiet, ↓reduceIte]
  | @foreign before after prior joint legal moved script mass owner different acting previous
      previousTrace previousReplay _related kernel atoms _description choice member earlier ih =>
    obtain ⟨action, actionEq, tagEq⟩ := sourceReplayCallbackAtoms_readback
      (setup := setup) (values := values) (implementation := implementation)
        scale owner previous.execution target reference ((joint owner).getD ⟨none⟩)
          kernel atoms choice member
    simp only [sourceRawReplay, previousReplay, Option.bind_some, acting,
      ite_eq_right different, actionEq] at replayed
    obtain ⟨priorEq, stateEq⟩ := sourceReplayAppend_prior_state setup implementation
      ⟨some previous, previousTrace⟩ actual _ _ replayed
    have latest := sourceReplayLastAction_respond setup implementation owner previous action
      actual stateEq
    have previousRead := ih ⟨some previous, previousTrace⟩ previousReplay
    simp only [sourceRawReplayReadback, priorEq, previousRead, Option.bind_some,
      ReactiveApplication.actor, acting, ite_eq_right different, latest, Option.map_some, tagEq]
    exact congrArg (fun selected => some ((choice.1, selected) :: script)) actionEq.symm

/-- Two supported sequential scripts that replay to the same actual raw
history have identical literal choices at every original slot. -/
theorem SourceRawReplayLaw.replay_injective
    (scale : Set.Icc (0 : ℝ) 1) (who : Player)
    (target : setup.proposalRecoveryProtocol.History) (reference : (nativeApplication).Control)
    (original : (nativeProtocol).History)
    (law : SourceRawReplayLaw (setup := setup) (values := values)
      (implementation := implementation) scale who target reference original)
    (first second : List (RawReplayChoice setup implementation))
    (firstSupported : first ∈ law.choices.support) (secondSupported : second ∈ law.choices.support)
    (actual : (nativeProtocol).History)
    (firstReplay : sourceRawReplay setup implementation who target reference original first =
      some actual)
    (secondReplay : sourceRawReplay setup implementation who target reference original second =
      some actual) : first = second := by
  have firstRead := sourceRawReplay_readback setup values implementation scale who target reference
    original first (law.choices first) (law.atoms first firstSupported) actual firstReplay
  have secondRead := sourceRawReplay_readback setup values implementation scale who target reference
    original second (law.choices second) (law.atoms second secondSupported) actual secondReplay
  exact Option.some.inj (firstRead.symm.trans secondRead)

end Vegas.PhaseProposalQualifiedBinding
