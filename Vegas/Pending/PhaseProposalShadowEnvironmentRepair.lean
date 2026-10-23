/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowIncludeRepair
import Vegas.Pending.PhaseProposalShadowEnvironment
import Vegas.Pending.PhaseProposalShadowActivation

/-! # Every actual environment command extends the general counted repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The selected real scheduler command and its realized original outcome
construct the actual repaired counted successor. All application and network
commands are included, with no clear-state or surviving-owner restriction. -/
theorem environment_repair
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (left right : (app).Execution)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, left⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining + 1, none, right⟩))
    (memory : BindingShadow graph) (owner : Player)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (supported : memory.CompletedAt right.application.current.native.config)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (prepared : PreparedBindings runtime leaks owner left right)
    (entryRef : left.application.entry.native.config.store.BindingRefines
      right.application.entry.native.config.store)
    (currentRef : left.application.current.native.config.store.BindingRefines
      right.application.current.native.config.store)
    (command : (app).Command)
    (selected : command ∈ (scheduler left.environmentRecall (left.observeEnvironment app)).support)
    (next : (app).Execution) (moved : next ∈ (left.environmentStep app command).support) :
    ∃ (nextMemory : BindingShadow graph) (image : (app).Execution),
      image ∈ (right.environmentStep app command).support ∧
      Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨remaining, command.actor? app, image⟩)) ∧
      nextMemory.OwnBindings owner ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame nextMemory owner next.application image.application ∧
      nextMemory.CompletedAt image.application.current.native.config ∧
      next.network = image.network ∧
      phaseExternalObservation runtime leaks owner next =
        phaseExternalObservation runtime leaks owner image ∧
      PreparedBindings runtime leaks owner next image ∧
      next.application.entry.native.config.store.BindingRefines
          image.application.entry.native.config.store ∧
      next.application.current.native.config.store.BindingRefines
          image.application.current.native.config.store := by
  classical
  have before : left.observeEnvironment app = right.observeEnvironment app := by
    change (⟨left.network.publicView, left.application.publicView, left.receipts⟩ :
      (app).EnvironmentView) = ⟨_, _, _⟩
    rw [network, receipts, frame.publicView owned]
    rfl
  have chosen : command ∈
      (scheduler right.environmentRecall (right.observeEnvironment app)).support := by
    rw [← service, ← before]
    exact selected
  cases command with
  | application command =>
      obtain ⟨nextMemory, image, imageMoved, nextOwned, candidates, paired, nextSupport,
          nextNetwork, external, refinement⟩ :=
        environment_external_repair runtime leaks memory owner owned left right frame supported
          network receipts service recalled command next moved
      have target := (PhaseCount.onePacketMenu runtime leaks bounds).trace_environment
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler remaining right image
          (.application command) rightTrace chosen imageMoved
      refine ⟨nextMemory, image, imageMoved, target, nextOwned, ?_, paired, nextSupport,
        nextNetwork, external, ?_, (refinement entryRef currentRef).1,
        (refinement entryRef currentRef).2⟩
      · intro slot
        rw [candidates]
        exact valid slot
      · exact PreparedBindings.environment runtime leaks prepared (.application command)
          moved imageMoved
  | «include» id =>
      rw [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at moved
      subst next
      obtain ⟨nextMemory, target, nextOwned, nextValid, paired, nextSupport, nextNetwork,
          external, nextPrepared, nextEntryRef, nextCurrentRef⟩ :=
        include_repair runtime leaks bounds plan inputs horizon scheduler remaining left right
          leftTrace rightTrace memory owner frame owned valid supported network receipts service
            recalled prepared entryRef currentRef id selected
      refine ⟨nextMemory, _, ?_, target, nextOwned, nextValid, paired, nextSupport, nextNetwork,
        external, nextPrepared, nextEntryRef, nextCurrentRef⟩
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff]
  | activate actor =>
      obtain ⟨coupled, leftLaw, rightLaw, properties⟩ :=
        activation_external_coupling runtime leaks memory owner owned left right frame network
          receipts service recalled actor
      have supportedLeft : next ∈ (coupled.map Prod.fst).support := by rw [leftLaw]; exact moved
      obtain ⟨pair, drawn, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supportedLeft
      rcases pair with ⟨first, image⟩
      change first = next at same
      subst first
      obtain ⟨paired, nextNetwork, _leftRecall, _rightRecall, external, leftApplication,
          rightApplication⟩ := properties (next, image) drawn
      have imageMoved : image ∈ (right.environmentStep app (.activate actor)).support := by
        rw [← rightLaw]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨(next, image), drawn, rfl⟩
      have target := (PhaseCount.onePacketMenu runtime leaks bounds).trace_environment
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler remaining right image
          (.activate actor) rightTrace chosen imageMoved
      refine ⟨memory, image, imageMoved, target, owned, valid, paired, ?_, nextNetwork,
        external, ?_, ?_, ?_⟩
      · rw [rightApplication]
        exact supported
      · exact PreparedBindings.environment runtime leaks prepared (.activate actor) moved imageMoved
      · rw [leftApplication, rightApplication]
        exact entryRef
      · rw [leftApplication, rightApplication]
        exact currentRef
  | wait =>
      rw [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at moved
      subst next
      let image : (app).Execution := { right with
        environmentRecall := right.environmentRecall ++ [⟨right.observeEnvironment app, .wait⟩] }
      have imageMoved : image ∈ (right.environmentStep app .wait).support := by
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff]
        rfl
      have sourceMoved : { left with environmentRecall := left.environmentRecall ++
          [⟨left.observeEnvironment app, .wait⟩] } ∈ (left.environmentStep app .wait).support := by
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff]
      have target := (PhaseCount.onePacketMenu runtime leaks bounds).trace_environment
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler remaining right image
          .wait rightTrace chosen imageMoved
      refine ⟨memory, image, imageMoved, target, owned, valid, frame, supported, network, ?_,
        PreparedBindings.environment runtime leaks prepared .wait sourceMoved imageMoved,
        entryRef, currentRef⟩
      have nextService : left.environmentRecall ++ [⟨left.observeEnvironment app, .wait⟩] =
          right.environmentRecall ++ [⟨right.observeEnvironment app, .wait⟩] := by
        rw [service, before]
      exact phaseExternalObservation_congr runtime leaks
        { left with environmentRecall := left.environmentRecall ++
          [⟨left.observeEnvironment app, .wait⟩] }
        image owner network receipts nextService (frame.publicView owned)
          (frame.playerView_other owned) recalled

end Vegas.EventGraphRuntime.BindingShadow
