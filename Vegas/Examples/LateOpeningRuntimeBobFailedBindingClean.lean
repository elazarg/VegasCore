/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobBindingPacket
import Vegas.Examples.LateOpeningRuntimeBobBindingSettlement

/-! # Failed-publication binding cleanliness over the full information class

The actual maximizing response law is common to every compatible history.
One positively assessed clean settlement certifies its fixed public packet.
That certificate then applies to every legal hidden history, including those
assigned zero belief. It certifies the current prefix rather than future play.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobFailedBindingClean

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobBindingInformation LateOpeningRuntimeBobBindingDecision
  LateOpeningRuntimeBobBindingOptimization LateOpeningRuntimeBobBindingSettlement
  LateOpeningRuntimeBobBindingPacket LateOpeningRuntimeBobAudit
  LateOpeningRuntimeEarlyBobSafeMenu
open LateOpeningRuntimeBobRawBinding (serviced response_result_same_information)
open LateOpeningRuntimeBobBindingDecision (context)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)
  (reward forfeit : ℝ) (deposit : Player → ℝ)

/-- A supported maximizing response has the actual canonical public packet
and an accepting Bob-zero receipt throughout the complete native fiber. Its
private submission representation remains unrestricted. -/
theorem rational_supported_clean_binding (forfeitPositive : 0 < forfeit)
    (depositPositive : 0 < deposit bob)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalAt site
      (context weight nonnegative site reward forfeit deposit assessment))
    (response : app.Action)
    (supported : response ∈ (currentResponses weight nonnegative decision assessment).support) :
    ∃ material : app.Submission, ∃ answer : Answer,
      response = ⟨some material⟩ ∧
      responseMessage decision.execution material = LateOpeningRuntimeBobSuffix.bindingMessage ∧
      (serviced decision.execution response).application.config.store (.inr bobBindEvent) =
        some (.success answer) ∧
      (∃ bit : Bool, answer = bitGuess bit) ∧
      (context weight nonnegative site reward forfeit deposit assessment).value
        (answerFinitePolicy weight nonnegative answer) =
          bestGuessValue weight nonnegative site reward forfeit deposit assessment ∧
      ((bob, 0), true) ∈ (serviced decision.execution response).receipts ∧
      CleanBindings (serviced decision.execution response) ∧
      ∀ history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1,
        responseMessage (decisionOfInformation weight nonnegative site representative decision
          current history).execution material = LateOpeningRuntimeBobSuffix.bindingMessage ∧
        ((bob, 0), true) ∈ (serviced (decisionOfInformation weight nonnegative site representative
          decision current history).execution response).receipts ∧
        CleanBindings (serviced (decisionOfInformation weight nonnegative site representative
          decision current history).execution response) := by
  obtain ⟨bit, selected, maximizing, clean⟩ := rational_supported_clean_settlement
    weight nonnegative site representative decision current reward forfeit deposit
      forfeitPositive depositPositive assessment rational response supported
  let answer : Answer := bitGuess bit
  have shape : ∃ bit : Bool, answer = bitGuess bit := ⟨bit, rfl⟩
  obtain ⟨history, believed⟩ := (assessment.belief bob site).support_nonempty
  let recovered := decisionOfInformation weight nonnegative site representative decision current
    history
  have compatible := decisionOfInformation_spec weight nonnegative site representative decision
    current history
  have same := response_result_same_information weight nonnegative decision recovered
    compatible.2.1 compatible.2.2 response
  have selectedHere := same.symm.trans selected
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy
  obtain ⟨final, reached⟩ := (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 14 (recovered.execution.respond app bob response)).support_nonempty
  have clear := (clean history believed final reached).2
  obtain ⟨material, responseEq, packetHere⟩ := packet_canonical_of_terminal_clear weight nonnegative
    recovered.execution recovered.trace recovered.quiet recovered.ready response answer selectedHere
      players final reached clear
  subst response
  have referencePacket : responseMessage decision.execution material =
      LateOpeningRuntimeBobSuffix.bindingMessage :=
    (responseMessage_same_information decision.execution recovered.execution
      (app.history_inputRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace)
      (app.history_inputRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) recovered.trace)
        compatible.2.1 compatible.2.2 material).trans packetHere
  obtain ⟨other, actionEq, _, _, receipt, _⟩ := accepted_response weight nonnegative
    decision.execution decision.trace decision.quiet decision.ready ⟨some material⟩ answer selected
  have materialEq : material = other := Option.some.inj
    (congrArg ReactiveApplication.Action.transmission actionEq)
  subst other
  refine ⟨material, answer, rfl, referencePacket, selected, shape, maximizing, receipt,
    canonical_packet_clean weight nonnegative decision.execution decision.trace decision.quiet
      decision.ready material answer selected referencePacket, ?_⟩
  intro hidden
  let next := decisionOfInformation weight nonnegative site representative decision current hidden
  have matching := decisionOfInformation_spec weight nonnegative site representative decision
    current hidden
  have nextPacket : responseMessage next.execution material =
      LateOpeningRuntimeBobSuffix.bindingMessage :=
    (responseMessage_same_information decision.execution next.execution
      (app.history_inputRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace)
      (app.history_inputRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) next.trace)
        matching.2.1 matching.2.2 material).symm.trans referencePacket
  have nextSelected := (response_result_same_information weight nonnegative decision next
    matching.2.1 matching.2.2 ⟨some material⟩).symm.trans selected
  obtain ⟨another, nextActionEq, _, _, nextReceipt, _⟩ := accepted_response weight nonnegative
    next.execution next.trace next.quiet next.ready ⟨some material⟩ answer nextSelected
  have nextMaterialEq : material = another := Option.some.inj
    (congrArg ReactiveApplication.Action.transmission nextActionEq)
  subst another
  exact ⟨nextPacket, nextReceipt,
    canonical_packet_clean weight nonnegative next.execution next.trace next.quiet next.ready
      material answer nextSelected nextPacket⟩

end Vegas.Examples.LateOpeningRuntimeBobFailedBindingClean
