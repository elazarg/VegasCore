/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateMasses

/-! # The content of a slot-tier response

Along every history of the one-packet game, at a binding of the player's turn,
committing a covered source choice at a slot the one-packet menu offers sends
a packet whose content factor is the as-if-honest mass of that choice
(`Vegas.contentFactor_slotResponse_bind`): the menu's count verdict leaves the
slot fresh, so the submitted value is the binding the packet commits, and it
decodes back to the choice.

So a transmitting choice of content factor zero is the slot-tier choice of no
supported source choice (`Vegas.slotChoiceOf_ne_of_zeroContent`), and the
as-if-honest choice, the slot tier, every late option and silence give it no
mass (`Vegas.tierMasses_of_zeroContent`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **The content of a slot-tier commitment.** Along every history of the
one-packet game, at a binding of the player's turn, an offered commitment of a
covered source choice at a slot has content factor the as-if-honest mass of the
choice. -/
theorem contentFactor_slotResponse_bind
    (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (slot : Nat) (choice : Option (OwnAction Player L))
    (covered : CoveredBinding setup bounds event choice)
    (member : slotResponse setup runtime leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who) event slot choice ∈
      bounds.onePacketActions runtime leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who)) :
    contentFactor setup runtime leaks assessment who control.execution
        (control.execution.respond (application setup runtime leaks) who
          (slotResponse setup runtime leaks who (control.execution.recall who)
            (control.execution.observe (application setup runtime leaks) who) event slot choice))
        (slotResponse setup runtime leaks who (control.execution.recall who)
          (control.execution.observe (application setup runtime leaks) who) event slot choice) =
      (asIfHonestProfile setup runtime leaks assessment who (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)) choice).toReal := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have recalled := runtime.countRecall_history leaks rawTrace
  obtain ⟨action, encoded, values⟩ := covered
  obtain ⟨value, successful, _⟩ := values who payload outputEq codeEq node
  obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup runtime leaks who
    (control.execution.recall who) (control.execution.observe (application setup runtime leaks) who)
    event node slot choice action encoded
  -- The count verdict leaves the slot fresh.
  obtain ⟨_, permitted⟩ := (bounds.mem_onePacketActions runtime leaks who _ _ _).mp member
  have verdict : CountPermits ((application setup runtime leaks).outputs (control.execution.recall
    who))
      (runtime.localEnvelope leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who) material) := by
    rcases permitted with silent | ⟨other, otherSends, counted⟩
    · rw [transmits] at silent
      cases silent
    · rw [transmits] at otherSends
      cases Option.some.inj otherSends
      exact (countPermits_eq_true_iff _ _).mp counted
  rw [envelope] at verdict
  have correct := verdict.2.1
  unfold CountCallCorrect at correct
  dsimp only [slotEnvelope] at correct
  obtain ⟨_, _, _, _, unused⟩ := correct
  have freshState : control.execution.application.candidates.lookup (who, .prepared slot) =
      .fresh := by
    refine ((preparedFresh_history (runtime := runtime) horizon scheduler rawTrace) who slot).mpr ?_
    rintro ⟨message, input, sender, committed, call⟩
    have output : message ∈ (application setup runtime leaks).outputs (control.execution.recall
      who) := by
      rw [← recalled.1 who]
      exact List.mem_filter.mpr ⟨input, by simp [sender]⟩
    have earlier := earlierOwnPacket_of_output rawTrace who
      ((application setup runtime leaks).packet ((application setup runtime leaks).submit
        control.execution.application who material) who (control.execution.network.known who)
          material) message output
    rw [← runtime.localEnvelope_eq_of_recall leaks control.execution recalled.1
      recalled.2.1 who material, envelope] at earlier
    exact unused message earlier committed call
  have fresh : (control.execution.observe (application setup runtime leaks)
    who).application.candidates
      (.prepared slot) = .fresh := freshState
  -- The response commits the value at the slot.
  have responseEq : slotResponse setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who) event slot choice =
      ⟨some ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩, .none⟩⟩ := by
    rw [slotResponse_of_bind setup runtime leaks who _ _ event node slot choice action encoded,
      runtime.reactiveBinding_normal_of_fresh leaks who _ _ event payload _ slot fresh,
      successful]
    rfl
  have result := submitted_bindingResult runtime leaks control.execution who event payload
    slot (some ⟨payload, value⟩) freshState
  have decoded : decodeEventAction setup.program event action = choice := by
    cases choice with
    | none => cases encoded
    | some source =>
        exact decodeEventAction_encodeEventAction?_eq_some setup.program event source action
          encoded
  have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (PublicationResult.success value : PublicationResult (L.Val payload)) := by
    rw [← successful]
    simp
  rw [responseEq]
  unfold contentFactor sentSourceAction
  dsimp only
  simp only [node]
  rw [result]
  simp only [Option.bind_some, Raw.as?_mk, Option.elim_some]
  rw [← actionEq, decoded]
  rfl

/-- **A zero-content commitment is no slot-tier choice of a supported source
choice.** At a covered pending binding of the player's turn, a transmitting
choice whose content factor is zero is the slot-tier choice of no source choice
as-if-honest play supports, at any slot. -/
theorem slotChoiceOf_ne_of_zeroContent
    (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (site : CoveredPendingBinding setup runtime leaks bounds assessment who
      (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who) event payload outputEq
        codeEq)
    (response : (application setup runtime leaks).Action) (transmits : response.transmission ≠ none)
    (zero : contentFactor setup runtime leaks assessment who control.execution
      (control.execution.respond (application setup runtime leaks) who response) response = 0)
    (choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)))
    (chosen : choice.1 = some response) (slot : Nat) (source : Option (OwnAction Player L))
    (supported : source ∈ (asIfHonestProfile setup runtime leaks assessment who
      (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who))).support) :
    slotChoiceOf setup runtime leaks bounds (initialLaw setup) horizon scheduler who
      (control.execution.recall who) (control.execution.observe (application setup runtime leaks)
        who)
      event slot source ≠ choice := by
  intro equal
  have values := congrArg Subtype.val equal
  rw [chosen] at values
  by_cases offered : slotResponse setup runtime leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who) event slot source ∈
      bounds.onePacketActions runtime leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who)
  · have offeredValue : (slotChoiceOf setup runtime leaks bounds (initialLaw setup) horizon
      scheduler who
        (control.execution.recall who) (control.execution.observe (application setup runtime
          leaks) who)
        event slot source).1 = some (slotResponse setup runtime leaks who
          (control.execution.recall who)
          (control.execution.observe (application setup runtime leaks) who) event slot source) := by
      simp only [slotChoiceOf, responseChoice, offered, ↓reduceDIte]
    rw [offeredValue] at values
    have responseEq := Option.some.inj values
    rw [← responseEq, contentFactor_slotResponse_bind (runtime := runtime) assessment trace who
      event site.node slot
      source (site.covered source supported) offered] at zero
    have positive := (PMF.mem_support_iff _ _).mp supported
    exact positive ((ENNReal.toReal_eq_zero_iff _).mp zero |>.resolve_right
      (PMF.apply_ne_top _ _))
  · have silentValue : (slotChoiceOf setup runtime leaks bounds (initialLaw setup) horizon
      scheduler who
        (control.execution.recall who) (control.execution.observe (application setup runtime
          leaks) who)
        event slot source).1 = some ⟨none⟩ := by
      simp only [slotChoiceOf, responseChoice, offered, ↓reduceDIte]
    rw [silentValue] at values
    have responseEq := Option.some.inj values
    rw [← responseEq] at transmits
    exact transmits rfl

/-- **Zero-content commitments have no prescribed mass.** At a covered pending
binding of the player's turn, a transmitting choice of content factor zero has
no mass under the as-if-honest choice, the slot tier, any late option, or
silence. -/
theorem tierMasses_of_zeroContent
    (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (site : CoveredPendingBinding setup runtime leaks bounds assessment who
      (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who) event payload outputEq
        codeEq)
    (response : (application setup runtime leaks).Action) (transmits : response.transmission ≠ none)
    (zero : contentFactor setup runtime leaks assessment who control.execution
      (control.execution.respond (application setup runtime leaks) who response) response = 0)
    (choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice who
      (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)))
    (chosen : choice.1 = some response) :
    honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
      choice =
        0 ∧
      slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who _
        choice =
        0 ∧
      (∀ {slots : Nat} (option : LateOption slots),
        lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who
          _ option
          choice = 0) ∧
      PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler who _)
        choice = 0 := by
  have avoided := slotChoiceOf_ne_of_zeroContent (runtime := runtime) assessment trace who event
    site response
    transmits zero choice chosen
  have silenceNe : silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler who
      (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)) ≠ choice := by
    intro equal
    have values := congrArg Subtype.val equal
    rw [chosen] at values
    have silentValue : (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon
      scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup runtime leaks) who))).1 = some ⟨none⟩ := by
      simp only [silenceChoice, responseChoice,
        bounds.silence_onePacket runtime leaks who, ↓reduceDIte]
    rw [silentValue] at values
    have responseEq := Option.some.inj values
    rw [← responseEq] at transmits
    exact transmits rfl
  obtain ⟨canonical, selected⟩ := onePacket_canonicalFreshSlot_exists (runtime := runtime) trace who
  refine ⟨?_, ?_, fun option => ?_, PMF.pure_apply_of_ne _ _ silenceNe.symm⟩
  · change (honestResponse setup runtime leaks assessment who _ _).map _ choice = 0
    rw [honestResponse_eq_slotResponse setup runtime leaks assessment who _ _ event site.turn
      site.node
      canonical selected, PMF.map_comp]
    exact map_apply_eq_zero_of_forall_ne _ _ _ fun source supported =>
      avoided canonical source supported
  · rw [slotChoice_eq_map (runtime := runtime) (initialLaw setup) horizon scheduler site.turn]
    refine map_apply_eq_zero_of_forall_ne _ _ _ fun pair pairSupported => ?_
    obtain ⟨pairSlot, _, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp pairSupported
    obtain ⟨pairSource, sourceSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
    exact avoided pairSlot pairSource sourceSupported
  · cases option with
    | none =>
        rw [lateChoice_none]
        exact PMF.pure_apply_of_ne _ _ silenceNe.symm
    | some slot =>
        rw [lateChoice_some_eq_map (runtime := runtime) assessment who _ _ event site.turn slot]
        exact map_apply_eq_zero_of_forall_ne _ _ _ fun source supported =>
          avoided slot.val source supported

end Vegas
