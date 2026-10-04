/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePendingSegment
import Vegas.Pending.ReactiveUnusableBinding
import Vegas.Pending.ReactiveAsyncContract
import Vegas.Game.SourceServiceRetainedLocalSlots
import Vegas.Game.SourceServicePendingCommitmentLedger

/-! # The actual unusable response seeds its pending segment

The original action is a full effective response, not a future risk-policy
promise. At the real clear repaired prefix its absent or mistyped material
selects the retained typed default. Actual registration and emission derive
all resources of the one pending event, including its allocated anchor and
locally remembered failed result.

Complete play excludes a still-ready pending event at the real terminal
budget. The existing finite coupling therefore reaches actual settlement or
a classified owner draw. Independent actual tails preserve both complete
marginals. This does not compare utilities or share a postsettlement path.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Actual typed-default selection supplies the entire pending-segment seed.
The number of subsequent rounds is the original RAW control's real remaining
budget. The first shared boundary is actual settlement or a classified owner
response, after which the theorem retains actual checkpoint and tail support
rather than asserting a common future continuation. The actual implementation
reference stays fixed across this segment and its later tails. -/
theorem sourceServiceMissing_unusable_pending_stopped_coupling
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (values : bounds.CoversBindingValues)
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (onlyBindings : memory.shadow.OwnBindings who)
    (past : memory.shadow.CompletedAt original.application.config)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, some who, original⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, some who, repaired⟩))
    (rightAtTurn : OwnSubmissionsAtTurn setup leaks repaired who)
    (rightSlots : CanonicalSlotsUsed setup leaks repaired who)
    (clear : (runtime setup).serviceRisk leaks bound who (repaired.recall who)
      (repaired.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (original.recall who) (original.observe (application setup leaks) who))
    (unusable : unusableServiceBindingResponse setup leaks who (repaired.recall who)
      (repaired.observe (application setup leaks) who) response)
    (players : Player → (application setup leaks).Policy)
    (reference : List (application setup leaks).PlayerEntry)
    (referenceStarted : reference.length ≤ (repaired.recall who).length) :
    let app := application setup leaks
    let input := (repaired.recall who, repaired.observe app who)
    let selected := BindingMemory.retainedResponse (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who memory input response
    let remembered : BindingMemory (runtime setup) leaks :=
      ⟨selected.2, memory.responses ++ [(memory.shadow.inputView (runtime setup) leaks
        input.2, response)]⟩
    let left := original.respond app who response
    let right := repaired.respond app who selected.1
    let strategy := BindingMemory.retainedImplementation (runtime setup) leaks
      (bounds.riskMenu (runtime setup) leaks bound) who reference (players who)
    ∃ event, (runtime setup).submittedEvent? leaks response = some event ∧
      let boundary := fun next : app.Execution × app.Execution ×
          BindingMemory (runtime setup) leaks =>
        (next.2.2.Frame (runtime setup) leaks who next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings who ∧ next.2.2.shadow.CompletedAt
            next.1.application.config ∧ event ∈ next.1.application.config.cut.completed ∧
          OwnerCommitmentsInertOrMatching who next.1 next.2.1 ∧
          OwnSubmissionsAtTurn setup leaks next.2.1 who ∧
          CanonicalSlotsUsed setup leaks next.2.1 who) ∨
          ∃ budget before chosen,
            Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
              (some ⟨budget, some who, before⟩)) ∧
            chosen ∈ (players who (before.recall who) (before.observe app who)).support ∧
            next.1 = before.respond app who chosen ∧
            (auditableServiceResponse setup leaks who (before.recall who)
              (before.observe app who) chosen ∨
                recordedServiceResponse setup leaks (before.recall who) chosen)
      ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory (runtime setup) leaks),
        coupling.map Prod.fst = app.runRounds scheduler players leftRemaining left ∧
        coupling.map Prod.snd =
          strategy.runJoint who players scheduler leftRemaining right remembered ∧
        ∀ next ∈ coupling.support,
          ∃ stopped ≤ leftRemaining,
            ∃ checkpoint : app.Execution × app.Execution × BindingMemory (runtime setup) leaks,
              checkpoint.1 ∈ (app.runRounds scheduler players stopped left).support ∧
              checkpoint.2 ∈
                (strategy.runJoint who players scheduler stopped right remembered).support ∧
              boundary checkpoint ∧
              Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
                (some ⟨leftRemaining - stopped, none, checkpoint.1⟩)) ∧
              Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
                (some ⟨leftRemaining - stopped, none, checkpoint.2.1⟩)) ∧
              ((runtime setup).persistentServiceRisk leaks bound who (checkpoint.2.1.recall who)
                  (checkpoint.2.1.observe app who) = false →
                OwnSubmissionsAtTurn setup leaks checkpoint.2.1 who ∧
                  CanonicalSlotsUsed setup leaks checkpoint.2.1 who) ∧
              next.1 ∈
                (app.runRounds scheduler players (leftRemaining - stopped) checkpoint.1).support ∧
              next.2 ∈ (strategy.runJoint who players scheduler (leftRemaining - stopped)
                checkpoint.2.1 checkpoint.2.2).support := by
  classical
  let app := application setup leaks
  let view := repaired.observe app who
  let input := (repaired.recall who, view)
  let selected := BindingMemory.retainedResponse (runtime setup) leaks
    (bounds.riskMenu (runtime setup) leaks bound) who memory input response
  let remembered : BindingMemory (runtime setup) leaks :=
    ⟨selected.2, memory.responses ++ [(memory.shadow.inputView (runtime setup) leaks
      input.2, response)]⟩
  let left := original.respond app who response
  let right := repaired.respond app who selected.1
  have chosen := sourceServiceMissing_unusable_default_retained bounds bound values original
    repaired who memory frame rightTrace rightAtTurn rightSlots clear response effective unusable
  have submitted := sourceServiceMissing_unusable_default_frame bounds bound values original
    repaired who memory frame onlyBindings past leftTrace rightTrace rightAtTurn rightSlots clear
      response effective
      unusable
  obtain ⟨event, payload, outputEq, codeEq, node, turn, unrecorded, opening, responseEq,
    missing⟩ := unusable
  let serial := repaired.application.publicView.bindingCount who
  let candidate : Handle (graph setup) := (who, .prepared serial)
  let id : MessageId Player := (who, original.network.nextSerial who)
  let message : Message Player (WitnessedPacket (graph setup)) :=
    ⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩
  let material : app.Submission := ⟨⟨.commitment event candidate, opening⟩, .none⟩
  let anchor : app.PlayerEntry := ⟨original.observe app who, response, some message⟩
  change response = ⟨some material⟩ at responseEq
  have named : (runtime setup).submittedEvent? leaks response = some event := by
    rw [responseEq]
    rfl
  have residual : unusableServiceBindingResponse setup leaks who (repaired.recall who)
      (repaired.observe app who) response :=
    ⟨event, payload, outputEq, codeEq, node, turn, unrecorded, opening, responseEq, missing⟩
  have pending := sourceServiceMissing_unusable_default_completedExcept bounds bound values
    original repaired who memory frame past rightTrace rightAtTurn rightSlots clear response
      effective residual event named
  have afterFrame : remembered.Frame (runtime setup) leaks who left right := submitted.1
  have afterOwn : remembered.shadow.OwnBindings who := submitted.2.1
  have afterPast : remembered.shadow.CompletedExcept left.application.config event := pending
  have rightFresh := canonicalSlot_fresh_of_used rightTrace who rightAtTurn rightSlots event turn
    unrecorded
  have fresh : original.application.candidates.lookup candidate = .fresh :=
    (frame.slots (.prepared serial)).mpr rightFresh
  have ownFresh : (memory.shadow.inputView (runtime setup) leaks view).application.candidates
      (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  have rightReady := (repaired.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec repaired.application.publicView who event turn).1
  have ready : original.application.config.cut.Ready event := by
    rw [← State.publicView_eventReady, frame.publicView, State.publicView_eventReady]
    exact rightReady
  have unchanged := (runtime setup).reactive_respond_application leaks original who response
  have afterReady : left.application.config.cut.Ready event := by rwa [unchanged.1]
  have leftFixed : left.application.candidates.lookup candidate ≠ .fresh := by
    intro lookup
    change (original.respond app who response).application.candidates.lookup candidate =
      .fresh at lookup
    rw [responseEq] at lookup
    have impossible := ((runtime setup).submitted_binding_fresh_iff leaks original who event
      serial opening (.prepared serial)).mp lookup |>.1
    exact impossible rfl
  have rightFixed : right.application.candidates.lookup candidate ≠ .fresh := by
    intro lookup
    exact leftFixed ((afterFrame.slots (.prepared serial)).mpr lookup)
  have failed : left.application.bindingResult candidate payload = .failure := by
    have result := (runtime setup).submitted_bindingResult leaks original who event payload
      serial opening fresh
    change (original.respond app who response).application.bindingResult candidate payload = _
    rw [responseEq]
    rw [missing] at result
    exact result
  have rememberedFailure := BindingMemory.repairResponse_unusable_shadow_failure who memory view
    event payload outputEq codeEq node serial opening ownFresh rightFresh missing
  have selectedEq : selected = memory.repairResponse (runtime setup) leaks who view
      ⟨some material⟩ := chosen.1.trans
        (congrArg (memory.repairResponse (runtime setup) leaks who view) responseEq)
  have rememberedAction : remembered.shadow.actions event = some
      (cast (congrArg EventField.Action outputEq.symm) PublicationResult.failure) := by
    exact (congrArg (fun change => change.2.actions event) selectedEq).trans rememberedFailure.1
  have rememberedValue : remembered.shadow.values (.inr event) = some
      (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure) := by
    exact (congrArg (fun change => change.2.values (.inr event)) selectedEq).trans
      rememberedFailure.2
  have packet : app.packet (app.submit original.application who material) who
      (original.network.known who) material = message.payload := by
    rw [reactiveApplication_packet_none,
      original.application.publicView_tokenFor_of_ready _ event rfl ready]
  have split : left.recall who = original.recall who ++ anchor :: [] := by
    change (original.respond app who response).recall who =
      original.recall who ++ [⟨original.observe app who, response, some message⟩]
    rw [show response = ⟨some material⟩ from responseEq]
    simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
    rw [packet]
    rfl
  have earlierUnrecorded : (runtime setup).eventRecorded leaks (original.recall who) event =
      false := ((runtime setup).eventRecorded_congr leaks _ _ frame.submissions event).trans
        unrecorded
  have started : reference.length ≤ (right.recall who).length := by
    rw [app.respond_recall_length]
    simp only [ite_true]
    exact referenceStarted.trans (Nat.le_add_right _ _)
  obtain ⟨afterTrace⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler leftRemaining
    original who response leftTrace
  have leftAccounted := app.raw_trace_accounted (initialLaw setup) horizon scheduler leftTrace
  have rightAccounted := app.raw_trace_accounted (initialLaw setup) horizon scheduler rightTrace
  change original.environmentRecall.length + leftRemaining = horizon at leftAccounted
  change repaired.environmentRecall.length + rightRemaining = horizon at rightAccounted
  rw [← frame.service] at rightAccounted
  have sameBudget : rightRemaining = leftRemaining := by omega
  obtain ⟨rightAfterTrace⟩ := app.raw_trace_respond (initialLaw setup) horizon scheduler
    rightRemaining repaired who selected.1 rightTrace
  have rightAfterSlots : (runtime setup).persistentServiceRisk leaks bound who (right.recall who)
        (right.observe app who) = false →
      OwnSubmissionsAtTurn setup leaks right who ∧ CanonicalSlotsUsed setup leaks right who := by
    intro persistent
    apply riskCanonicalSlots_respond bounds bound repaired who who selected.1 rightTrace
      (fun _ => ⟨rightAtTurn, rightSlots⟩) _ persistent
    intro _
    have same : selected.1 =
        (memory.repairResponse (runtime setup) leaks who view response).1 :=
      congrArg Prod.fst chosen.1
    exact same.symm ▸ chosen.2.1
  have retained : selected.1 ∈ bounds.canonicalActions (runtime setup) leaks who
      (repaired.recall who) (repaired.observe app who) := by
    have member : selected.1 ∈ bounds.riskActions (runtime setup) leaks bound who
        (repaired.recall who) (repaired.observe app who) := by
      have same : selected.1 =
          (memory.repairResponse (runtime setup) leaks who view response).1 :=
        congrArg Prod.fst chosen.1
      exact same.symm ▸ chosen.2.1
    rwa [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clear] at member
  have afterAtTurn := retainedOwnSubmissionsAtTurn_respond bounds repaired who selected.1
    retained rightAtTurn
  have afterSlots := retainedCanonicalSlots_respond bounds rightTrace retained rightAtTurn
    rightSlots
  have coupled := sourceService_pending_stopped_coupling bounds bound left right who remembered
    afterFrame afterTrace afterOwn event afterPast payload outputEq codeEq node afterReady id
      candidate leftFixed rightFixed failed rememberedAction rememberedValue anchor
        (original.recall who) [] split named earlierUnrecorded (by simp) rfl players
          reference started afterAtTurn afterSlots leftRemaining (Nat.le_refl _)
  dsimp only
  obtain ⟨coupling, first, second, related⟩ := coupled
  refine ⟨event, named, coupling, first, second, ?_⟩
  intro next member
  rcases related next member with pending | exited
  · have reached : next.1 ∈ (app.runRounds scheduler players leftRemaining left).support := by
      rw [← first, PMF.support_map]
      exact ⟨next, member, rfl⟩
    obtain ⟨terminalTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler
      players 0 leftRemaining left next.1
        (by simpa only [Nat.zero_add] using afterTrace) reached
    have terminal := complete ⟨0, none, next.1⟩ terminalTrace (by
      change 0 = 0 ∧ _
      exact ⟨rfl, rfl⟩)
    change next.1.application.config.cut.completed = Finset.univ at terminal
    exfalso
    apply pending.2.2.2.1.1
    rw [terminal]
    exact Finset.mem_univ _
  · obtain ⟨stopped, bounded, checkpoint, leftReached, rightReached, boundary, leftTail,
      rightTail⟩ := exited
    have accounted : leftRemaining - stopped + stopped = leftRemaining :=
      Nat.sub_add_cancel bounded
    have checkpointLeft := app.raw_trace_runRounds (initialLaw setup) horizon scheduler players
      (leftRemaining - stopped) stopped left checkpoint.1 (accounted.symm ▸ afterTrace)
        leftReached
    have checkpointRight := sourceServiceRetained_runJoint_slots bounds bound
      (horizon := horizon) (remaining := leftRemaining - stopped) stopped right who remembered
        (by simpa only [accounted, sameBudget] using rightAfterTrace) rightAfterSlots players
          reference checkpoint.2 rightReached
    have boundaryWithLedger :
        (checkpoint.2.2.Frame (runtime setup) leaks who checkpoint.1 checkpoint.2.1 ∧
          checkpoint.2.2.shadow.OwnBindings who ∧ checkpoint.2.2.shadow.CompletedAt
            checkpoint.1.application.config ∧
          event ∈ checkpoint.1.application.config.cut.completed ∧
          OwnerCommitmentsInertOrMatching who checkpoint.1 checkpoint.2.1 ∧
          OwnSubmissionsAtTurn setup leaks checkpoint.2.1 who ∧
          CanonicalSlotsUsed setup leaks checkpoint.2.1 who) ∨
        ∃ budget before chosen,
          Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
            (some ⟨budget, some who, before⟩)) ∧
          chosen ∈ (players who (before.recall who) (before.observe app who)).support ∧
          checkpoint.1 = before.respond app who chosen ∧
          (auditableServiceResponse setup leaks who (before.recall who)
            (before.observe app who) chosen ∨
              recordedServiceResponse setup leaks (before.recall who) chosen) := by
      rcases boundary with settled | classified
      · obtain ⟨settledFrame, settledOwn, settledPast, completed, settledAtTurn, settledSlots,
          laterNext, recallEq, laterSilent⟩ := settled
        obtain ⟨actualTrace⟩ := checkpointLeft
        have originalAtTurn := sourceServiceFrame_ownSubmissionsAtTurn
          ⟨leftRemaining, some who, original⟩ ⟨rightRemaining, some who, repaired⟩ who memory frame
            leftTrace rightTrace rightAtTurn
        have originalTurn : original.application.publicView.ownTurn? who = some event := by
          rw [frame.publicView]
          exact turn
        have ledger := sourceService_pending_completed_commitment_ledger original checkpoint.1
          checkpoint.2.1 who leftTrace actualTrace originalAtTurn event originalTurn
            earlierUnrecorded response players stopped leftReached anchor named laterNext recallEq
              laterSilent completed
        exact Or.inl ⟨settledFrame, settledOwn, settledPast, completed, ledger, settledAtTurn,
          settledSlots⟩
      · exact Or.inr classified
    exact ⟨stopped, bounded, checkpoint, leftReached, rightReached, boundaryWithLedger,
      checkpointLeft, checkpointRight.1, checkpointRight.2, leftTail, rightTail⟩

end Vegas
