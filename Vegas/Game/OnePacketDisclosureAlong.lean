/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDisclosureResolves
import Vegas.Game.OnePacketSpliceForced

/-! # Disclosures resolve along a history at a forced site

Take a history `h` ending at an own turn of `who`, with decoded point `p` that
`who` observes like an intended point `w`. A player `r ≠ who` may owe a failure
along `h`, so the argument for states forced for the observer
(`Vegas.disclosureResolves_of_forced`) does not apply to it. Its pending reveals
still resolve (`Vegas.disclosureResolves_along`):

* graph events complete in program order, including automatic service, so a ready reveal whose
  resolution fails at a state stays ready until it completes, and completing it,
  disclosing or not, stores a failed publication, a failed reveal of its owner at
  the decoded point (`Vegas.revealFailed_of_failing_step`), which persists
  (`Vegas.revealFailed_along`);
* at the end of `h` every ready reveal is `who`'s, so the reveal has completed,
  and a failed reveal is a publication `who` would observe at `w` too, where none
  failed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **Completing a failing reveal fails it.** From a configuration with a source
residual at which a reveal of `owner` is ready and resolves to a failure whether
disclosed or not, every completion of the reveal decodes to a point at which
`owner`'s reveal failed. -/
theorem revealFailed_of_failing_step {profile : BehavioralProfile setup.program} {rank : Nat}
    {config after : (graph setup).Config} (residual : SourceResidual setup profile rank config)
    {event : (graph setup).EventId} (ready : config.cut.Ready event) {owner : Player}
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (failing : ∀ disclose, EventGraph.EventCode.resolveOutput? binding checks disclose
      config.store = some .failure)
    (action : (graph setup).Action event)
    (member : after ∈ (config.step event ready action).support) :
    ∃ point, decodedPoint setup after = some point ∧
      ProtocolState.RevealFailed owner setup.program point := by
  set disclose : Bool := cast (congrArg EventGraph.EventField.Action outputEq) action
  have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose := by
    simp [disclose]
  have stepEq := config.step_eq_map_of_code event ready outputEq _ codeEq disclose
    (PMF.pure .failure) (by rw [EventGraph.EventCode.resolve_eval?, failing]; rfl)
  rw [actionEq, stepEq, PMF.pure_map, PMF.mem_support_pure_iff] at member
  have member' : after ∈ (config.step event ready action).support := by
    rw [actionEq, stepEq, PMF.pure_map, member]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨next, _⟩ := residual.step event ready action after member'
  have atEvent : config.cut.IsPrefix event.val :=
    ⟨event.isLt.le, fun query =>
      setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
  have atRank := atEvent.unique residual.checkpoint.ordered
  subst atRank
  have nextDecoded := next.decode
  unfold sourceServicePrefix? serviceSourcePrefix? at nextDecoded
  have owned : (graph setup).actor? event = some owner := nodeView_resolve_actor outputEq codeEq
  refine ⟨_, decodedPoint_eq next, ProtocolState.revealFailed_of_decode_failure setup.program
    event.val (event.val + 1) (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) _ _ _ _ event.isLt
    (Nat.lt_succ_self _) owner payload outputEq nextDecoded
    ((eventOwner?_eq_actor setup.program event).trans owned) ?_⟩
  rw [member]
  change (config.complete event ready _ _).outputs event = _
  rw [EventGraph.Config.complete_output_same]

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **A failing reveal fails or waits.** If a reveal of `owner` is ready at a
state of a history and resolves to a failure whether disclosed or not, then at
every later state of every extension the configuration is unchanged, or the
decoded point shows `owner`'s reveal failed. -/
theorem revealFailed_along {control : (application setup runtime leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (failing : ∀ disclose, EventGraph.EventCode.resolveOutput? binding checks disclose
      control.execution.application.config.store = some .failure) :
    ∀ {state} {trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
      state},
      TracePrefix prior trace → ∀ current : (application setup runtime leaks).Control,
        state = some current →
        current.execution.application.config = control.execution.application.config ∨
          ∃ point, decodedPoint setup current.execution.application.config = some point ∧
            ProtocolState.RevealFailed owner setup.program point := by
  have closed : StepClosed setup (ProtocolState.RevealFailed owner setup.program) :=
    fun state joint target failed reached =>
      ProtocolState.revealFailed_step owner setup.program state joint target failed reached
  have propagate {first last : (graph setup).Config} {rank : Nat}
      (residual : SourceResidual setup (failureProfile setup.program) rank first)
      (point : ProtocolState setup.program) (decoded : decodedPoint setup first = some point)
      (failed : ProtocolState.RevealFailed owner setup.program point)
      (path : Relation.ReflTransGen EventGraph.Config.Step first last) :
      ∃ next, decodedPoint setup last = some next ∧
        ProtocolState.RevealFailed owner setup.program next := by
    have holds : DecodedHolds (ProtocolState.RevealFailed owner setup.program) rank first := by
      intro next read
      rw [← decodedPoint_eq_of_isPrefix residual.checkpoint.ordered, decoded,
        Option.some.injEq] at read
      subst next
      exact failed
    obtain ⟨_, ⟨lastResidual⟩, lastHolds⟩ := residual.decodedHolds_path closed holds path
    exact ⟨_, decodedPoint_eq lastResidual, lastHolds _ lastResidual.decode⟩
  intro state trace isPrefix
  induction isPrefix with
  | refl =>
      intro current same
      cases same
      exact Or.inl rfl
  | @extend source target before earlier joint legal realized ih =>
      intro current same
      subst same
      cases source with
      | none => exact (not_tracePrefix_start (runtime := runtime) before earlier).elim
      | some previous =>
          have path := reactive_protocol_graph_steps runtime leaks (initialLaw setup) horizon
            scheduler previous current joint realized
          obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime)
            (failureProfile setup.program)
            (bounds.onePacketMenu runtime leaks) horizon scheduler before previous rfl
          rcases ih previous rfl with same | ⟨point, decoded, failed⟩
          · rcases path.cases_head with unchanged | ⟨middle, moved, rest⟩
            · exact Or.inl (unchanged.symm.trans same)
            · obtain ⟨other, otherReady, action, member⟩ := moved
              have readyPrevious : previous.execution.application.config.cut.Ready event :=
                by simpa only [same] using ready
              have failingPrevious : ∀ disclose, EventGraph.EventCode.resolveOutput? binding
                  checks disclose previous.execution.application.config.store =
                    some .failure := by simpa only [same] using failing
              have otherEq := setup.eventGraph.sequentialize_ready_unique _ otherReady
                readyPrevious
              subst otherEq
              obtain ⟨point, decoded, failed⟩ :=
                revealFailed_of_failing_step (outputEq := outputEq) (codeEq := codeEq)
                residual otherReady failingPrevious action member
              obtain ⟨nextResidual, _⟩ := residual.step _ otherReady action middle member
              exact Or.inr (propagate nextResidual point decoded failed rest)
          · exact Or.inr (propagate residual point decoded failed path)

/-- **Disclosures resolve along a history at a forced site.** For a well-formed
setup, take a history ending at a state `current` with decoded point `p`, at
which every ready reveal belongs to `who`, and the end `w` of an intended history
that `who` observes like `p`. At every state along the history, the canonical
disclosure of every player `r ≠ who` at its pending reveal transmits. -/
theorem disclosureResolves_along (wellFormed : setup.WellFormed) {who : Player}
    {current : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some current))
    {p w : ProtocolState setup.program}
    (decodedP : decodedPoint setup current.execution.application.config = some p)
    {second : setup.intendedProtocol.History} (secondState : second.state = some w)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program w)
    (readyOwn : ∀ event, current.execution.application.config.cut.Ready event →
      ∀ owner payload binding checks outputEq codeEq,
        nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
          owner = who)
    {control : (application setup runtime leaks).Control}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (isPrefix : TracePrefix prior trace) {r : Player} (different : r ≠ who) :
    DisclosureResolves setup runtime leaks r (control.execution.recall r)
      (control.execution.observe (application setup runtime leaks) r) := by
  intro event pending owner payload binding checks outputEq codeEq node
  obtain ⟨turn, _, owned, _⟩ := pendingEvent_spec (runtime := runtime) (setup := setup) pending
  have ownerEq : owner = r :=
    Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
  subst ownerEq
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      prior
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have ready : control.execution.application.config.cut.Ready event :=
    (control.execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ owner event turn).1
  have active := control.execution.application.active_of_ready_owned facts.quiescent ready owned
  have fieldsAvailable : ∀ field ∈ insert binding.field (EventGraph.GuardCheck.listReadFields
      checks), (control.execution.application.config.store field).isSome = true := by
    intro field member
    apply control.execution.application.config.read_available ready
    rw [← EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event), codeEq]
    exact member
  have available : (EventGraph.EventCode.resolveOutput? binding checks true
      control.execution.application.config.store).isSome = true :=
    EventGraph.EventCode.resolveOutput?_isSome binding checks true _ fieldsAvailable
  obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp available
  have discloses : (cast (congrArg EventGraph.EventField.Action outputEq)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) : Bool) = true := by
    simp
  cases result with
  | success value =>
      have stored := EventGraph.EventCode.binding_success_of_resolve_success binding checks true
        control.execution.application.config.store value resolved
      obtain ⟨candidate, accepted, candidateOwner, _verified, _packet⟩ :=
        EventGraphRuntime.reactiveResolutionPacket_provenance runtime leaks
          control.execution.application facts.binding owner event payload binding checks outputEq
          _ active discloses value stored
      apply runtime.canonicalServiceDecision_openable leaks owner
        (control.execution.recall owner)
        (control.execution.observe (application setup runtime leaks) owner) event owner payload
          binding checks outputEq codeEq node active value _ candidate accepted candidateOwner
      change binding.get? ((graph setup).playerStore owner
        control.execution.application.config.store) = _
      rw [EventGraph.FieldRef.get?_playerStore binding owner _ rfl, stored]
  | failure =>
      exfalso
      have failing : ∀ disclose, EventGraph.EventCode.resolveOutput? binding checks disclose
          control.execution.application.config.store = some .failure := by
        intro disclose
        cases disclose
        · exact EventGraph.EventCode.resolveOutput?_false_eq_failure binding checks _
            fieldsAvailable
        · exact resolved
      rcases revealFailed_along (runtime := runtime) (outputEq := outputEq) (codeEq := codeEq)
        prior ready failing
        isPrefix current rfl with same | ⟨point, decoded, failed⟩
      · have readyNow : current.execution.application.config.cut.Ready event := same ▸ ready
        exact different (readyOwn event readyNow owner payload binding checks outputEq codeEq
          node)
      · rw [decodedP, Option.some.injEq] at decoded
        subst decoded
        exact (forcedPoint_of_intended owner
          (intended_of_history wellFormed second.trace w secondState)).1
          ((ProtocolState.revealFailed_iff_of_observe_eq owner who setup.program _ _
            sameView).mp failed)

end Vegas
