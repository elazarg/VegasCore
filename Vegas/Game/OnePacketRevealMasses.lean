/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketStepGlue

/-! # The as-if-honest and slot laws at a reveal

Along every history of the one-packet game, at a reveal of the player's turn,
every source choice as-if-honest play supports encodes to the disclosure
(`Vegas.onePacket_honest_discloses`): the intended game never withholds. So the
as-if-honest law and the slot tier are both the canonical decision of the
disclosure (`Vegas.onePacket_honestChoice_reveal`,
`Vegas.onePacket_slotChoice_reveal`). When every publication value is a bounded
value and the player's recall has not submitted for the reveal, the one-packet
menu offers that decision whenever it transmits
(`Vegas.onePacket_disclosure_offered`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- Laws pushed along maps agreeing on the support agree. -/
private theorem map_congr_support {α β : Type} (law : PMF α) {f g : α → β}
    (agree : ∀ x ∈ law.support, f x = g x) : law.map f = law.map g := by
  ext b
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_congr fun x => ?_
  by_cases supported : x ∈ law.support
  · rw [agree x supported]
  · simp [(PMF.apply_eq_zero_iff law x).mpr supported]

/-- **As-if-honest play discloses.** Along every history of the one-packet game,
at a reveal of the player's turn, every source choice as-if-honest play
supports encodes to the disclosure. -/
theorem onePacket_honest_discloses (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .publication payload)
    (choice : Option (OwnAction Player L))
    (supported : choice ∈ (asIfHonestProfile setup leaks assessment who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))).support) :
    choice.bind (encodeEventAction? setup.program event) =
      some (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) := by
  obtain ⟨rank, point, ordered, decoded⟩ :=
    onePacket_decodes (setup.intendedOpeningProfile assessment.strategy) trace
  have encodes := asIfHonestProfile_encodes assessment who control.execution rank ordered point
    decoded _ event turn choice supported
  obtain ⟨action, encoded⟩ := Option.isSome_iff_exists.mp encodes
  rw [encoded]
  cases choice with
  | none => cases encoded
  | some source =>
      have back := decodeEventAction_encodeEventAction?_eq_some setup.program event source action
        encoded
      obtain ⟨noFailure, noWithholding⟩ := asIfHonestProfile_success assessment who
        control.execution rank ordered point decoded _ source supported
      generalize hdisclose : (cast (congrArg EventGraph.EventField.Action outputEq) action :
        Bool) = disclose
      have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
          disclose := by
        rw [← hdisclose]
        simp
      cases disclose with
      | true => rw [actionEq]
      | false =>
          exfalso
          have failing : Failing (decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)) :=
            decodeEventAction_failing_publication setup.program event.val (by exact event.isLt)
              (by exact outputEq)
          rw [← actionEq, back] at failing
          cases source with
          | commit sourceOwner name sourcePayload result =>
              have failed := failing.1 sourceOwner name sourcePayload result rfl
              subst failed
              exact noFailure sourceOwner name sourcePayload rfl
          | reveal sourceOwner name disclose =>
              have withheld : disclose = false := failing.2
              subst withheld
              exact noWithholding sourceOwner name rfl

/-- **The as-if-honest law at a reveal** is the canonical decision of the
disclosure. -/
theorem onePacket_honestChoice_reveal (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .publication payload) :
    honestChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) =
      PMF.pure (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))) := by
  change (honestResponse setup leaks assessment who _ _).map _ = _
  unfold honestResponse
  rw [show (control.execution.observe (application setup leaks) who).application.publicView.ownTurn?
    who = some event from turn]
  dsimp only
  rw [PMF.map_comp]
  rw [map_congr_support (g := fun _ => responseChoice setup leaks bounds (initialLaw setup) horizon
      scheduler who (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))
      ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))) _
    fun choice supported => by
      simp only [Function.comp_apply]
      rw [onePacket_honest_discloses assessment trace who event turn outputEq choice supported]]
  exact PMF.map_const _ _

/-- **The slot tier at a reveal** is the canonical decision of the disclosure. -/
theorem onePacket_slotChoice_reveal (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {owner : Player} {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout
      (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) =
      PMF.pure (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))) := by
  rw [slotChoice_eq_map (initialLaw setup) horizon scheduler turn]
  rw [map_congr_support (g := fun _ => responseChoice setup leaks bounds (initialLaw setup) horizon
      scheduler who (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))
      ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))) _
    fun pair supported => by
      obtain ⟨slot, _, inner⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      obtain ⟨choice, choiceDrawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp inner
      change responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who _
        (slotResponse setup leaks who _ _ event slot choice) = _
      unfold slotResponse
      rw [onePacket_honest_discloses assessment trace who event turn outputEq choice choiceDrawn]
      simp only [node]]
  exact PMF.map_const _ _

/-- **The disclosure is offered.** Along every history of the one-packet game,
at a reveal of the player's turn its recall has not submitted for, when every
publication value is a bounded value, the one-packet menu offers the canonical
decision of the disclosure whenever it transmits. -/
theorem onePacket_disclosure_offered (covers : bounds.CoversOutputValues)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event = false)
    {owner : Player} {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout
      (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (material : (application setup leaks).Submission)
    (sends : ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).transmission =
        some material) :
    (runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) ∈
      bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) := by
  classical
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have values := covers event
  rw [outputEq] at values
  have allowed : ∀ packet, reactiveResolutionPacket who event payload binding checks outputEq
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
      (control.execution.observe (application setup leaks) who).application = some packet →
        bounds.AllowsPacket packet := fun packet sent =>
    bounds.resolutionPacket_allowed who event payload binding checks outputEq _ _ values
      (fun field candidate accepted =>
        onePacket_accepted_allowed bounds trace field candidate accepted)
      packet sent
  have inMenu : (runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) ∈
        (bounds.menu (runtime setup) leaks).actions who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) := by
    apply bounds.canonicalServiceDecision_available (runtime setup) leaks who
    cases sent : reactiveResolutionPacket who event payload binding checks outputEq
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
        (control.execution.observe (application setup leaks) who).application with
    | none =>
        simp only [EventGraphRuntime.canonicalReactiveDecision, node, sent, Option.map_none]
        exact (ReactiveApplication.ResponseMenu.fromSubmissions_mem
          (app := (runtime setup).reactiveApplication leaks)
          (fun _ past view => bounds.submissions
            (ReactiveApplication.ResponseMenu.knownPackets past view)) who _ _ _).mpr trivial
    | some packet =>
        simp only [EventGraphRuntime.canonicalReactiveDecision, node, sent, Option.map_some]
        apply (ReactiveApplication.ResponseMenu.fromSubmissions_mem
          (app := (runtime setup).reactiveApplication leaks)
          (fun _ past view => bounds.submissions
            (ReactiveApplication.ResponseMenu.knownPackets past view)) who _ _ _).mpr
        have rawAllowed := bounds.disclosureSubmission_allowed _ [] (allowed packet sent)
        have normalized := (bounds.submissions_mem _ _).mp
          (bounds.normalize_submission_mem who
            (control.execution.observe (application setup leaks) who).application _ _
            ((bounds.submissions_mem _ _).mpr rawAllowed))
        exact (bounds.submissions_mem _ _).mpr
          ⟨normalized.1, bounds.allowsEvidence_mono (List.nil_subset _) _ normalized.2⟩
  have permits := canonicalServiceDecision_countPermits rawTrace who event turn unsent _ material
    sends
  exact (bounds.mem_onePacketActions (runtime setup) leaks who _ _ _).mpr
    ⟨inMenu, Or.inr ⟨material, sends, permits⟩⟩

end Vegas
