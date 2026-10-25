/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerLaws
import Vegas.Game.OnePacketOpeningUnique

/-! # The owner's opening law for slot-trembled late components

At a pending reveal of the owner's turn, the owner's resolution packet reads its
binding and public data only (`Vegas.reactiveResolutionPacket_congr`), so whether
the canonical disclosure transmits is read off the operational state. Along a
one-packet history the one-packet menu offers a transmitting disclosure exactly
when no own envelope names the reveal (`Vegas.disclosure_silent_iff`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A public field is visible to every player. -/
theorem publicStore_playerStore (who : Player) (store : EventGraph.Store (graph setup).layout) :
    (graph setup).publicStore ((graph setup).playerStore who store) =
      (graph setup).publicStore store := by
  funext field
  unfold EventGraph.publicStore EventGraph.playerStore
  by_cases isPublic : (graph setup).fieldPublic field
  · have visible : (graph setup).fieldVisibleTo who field := by
      unfold EventGraph.fieldPublic at isPublic
      unfold EventGraph.fieldVisibleTo
      generalize (graph setup).layout field = kind at isPublic ⊢
      cases kind <;> simp_all [EventGraph.EventField.IsPublic, EventGraph.EventField.VisibleTo]
    simp only [isPublic, visible, ↓reduceIte]
  · simp only [isPublic, ↓reduceIte]

/-- **The resolution packet reads the binding and public data.** At states with
the same operational state, with a publication event of the owner ready, the
owner's resolution packet of every action is the same. -/
theorem reactiveResolutionPacket_congr {first second : (application setup leaks).Control}
    (same : operationalState setup leaks (some first) = operationalState setup leaks (some second))
    {event : (graph setup).EventId} (ready : first.execution.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (action : (graph setup).Action event) :
    reactiveResolutionPacket owner event payload binding checks outputEq action
        (first.execution.observe (application setup leaks) owner).application =
      reactiveResolutionPacket owner event payload binding checks outputEq action
        (second.execution.observe (application setup leaks) owner).application := by
  have bindings := SameOperational.binding same ready view
  have publics := SameOperational.publicView same
  have stores : (graph setup).publicStore first.execution.application.config.store =
      (graph setup).publicStore second.execution.application.config.store :=
    congrArg (fun view : PublicView (graph setup) => view.observation.store) publics
  have own : ∀ store : EventGraph.Store (graph setup).layout,
      binding.get? ((graph setup).playerStore owner store) = binding.get? store := by
    intro store
    rcases binding with ⟨field, layoutEq⟩
    apply EventGraph.FieldRef.get?_congr
    apply EventGraph.playerStore_of_visible
    change ((graph setup).layout field).VisibleTo owner
    rw [layoutEq]
    rfl
  have resolved : EventGraph.EventCode.resolveOutput? binding checks true
      ((graph setup).playerStore owner first.execution.application.config.store) =
      EventGraph.EventCode.resolveOutput? binding checks true
        ((graph setup).playerStore owner second.execution.application.config.store) := by
    unfold EventGraph.EventCode.resolveOutput?
    rw [own, own, bindings]
    simp only [Option.bind_eq_bind]
    congr 1
    funext bound
    rw [← EventGraph.GuardCheck.allAccepted?_publicStore checks
        ((graph setup).playerStore owner first.execution.application.config.store),
      ← EventGraph.GuardCheck.allAccepted?_publicStore checks
        ((graph setup).playerStore owner second.execution.application.config.store),
      publicStore_playerStore, publicStore_playerStore, stores]
  have firstStore : (first.execution.observe (application setup leaks)
      owner).application.observation.store =
      (graph setup).playerStore owner first.execution.application.config.store := rfl
  have secondStore : (second.execution.observe (application setup leaks)
      owner).application.observation.store =
      (graph setup).playerStore owner second.execution.application.config.store := rfl
  have firstPublic : (first.execution.observe (application setup leaks)
      owner).application.publicView = first.execution.application.publicView := rfl
  have secondPublic : (second.execution.observe (application setup leaks)
      owner).application.publicView = second.execution.application.publicView := rfl
  unfold reactiveResolutionPacket
  rw [firstStore, secondStore, firstPublic, secondPublic]
  rw [resolved, publics]

/-- The canonical disclosure transmits exactly when the resolution packet
exists. -/
theorem disclosure_transmission_isSome (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) {event : (graph setup).EventId}
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (action : (graph setup).Action event) :
    ((runtime setup).canonicalServiceDecision leaks who past view event
        action).transmission.isSome =
      (reactiveResolutionPacket who event payload binding checks outputEq action
        view.application).isSome := by
  unfold EventGraphRuntime.canonicalServiceDecision
  cases packet : reactiveResolutionPacket who event payload binding checks outputEq action
      view.application with
  | none =>
      simp only [EventGraphRuntime.canonicalReactiveDecision, node, packet, Option.map_none,
        ReactiveApplication.SubmissionNormalization.action, Option.isSome_none]
  | some sent =>
      simp only [EventGraphRuntime.canonicalReactiveDecision, node, packet, Option.map_some,
        ReactiveApplication.SubmissionNormalization.action, Option.isSome_some]

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **When the disclosure is silent.** Along every history of the one-packet
game, at a reveal of the player's turn, when every publication value is a
bounded value, the chosen canonical disclosure keeps silence exactly when its
resolution packet is missing or an own envelope already names the reveal. -/
theorem disclosure_silent_iff (covers : bounds.CoversOutputValues)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    ((responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))).1.getD
          ⟨none⟩).transmission = none ↔
      ¬ ((reactiveResolutionPacket who event payload binding checks outputEq
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (control.execution.observe (application setup leaks) who).application).isSome ∧
        ¬ ∃ message ∈ (application setup leaks).outputs (control.execution.recall who),
          message.payload.call.event? (graph setup) = some event) := by
  set disclosure := (runtime setup).canonicalServiceDecision leaks who
    (control.execution.recall who) (control.execution.observe (application setup leaks) who) event
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) with disclosureEq
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have transmits := disclosure_transmission_isSome (leaks := leaks) who
    (control.execution.recall who) (control.execution.observe (application setup leaks) who) node
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
  rw [← disclosureEq] at transmits
  have decodedMember : ∀ response : (application setup leaks).Action,
      response ∈ bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) →
      (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) response).1.getD ⟨none⟩ =
        response := by
    intro response member
    simp only [responseChoice, member, ↓reduceDIte, Option.getD_some]
  have decodedSilent : ∀ response : (application setup leaks).Action,
      response ∉ bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) →
      (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) response).1.getD ⟨none⟩ =
        ⟨none⟩ := by
    intro response notMember
    simp only [responseChoice, notMember, ↓reduceDIte, Option.getD_some]
  cases sends : disclosure.transmission with
  | none =>
      rw [sends, Option.isSome_none] at transmits
      constructor
      · intro _ both
        rw [← transmits] at both
        cases both.1
      · intro _
        by_cases member : disclosure ∈ bounds.onePacketActions (runtime setup) leaks who
            (control.execution.recall who)
            (control.execution.observe (application setup leaks) who)
        · rw [decodedMember _ member]
          exact sends
        · rw [decodedSilent _ member]
  | some material =>
      rw [sends, Option.isSome_some] at transmits
      by_cases unsent : (runtime setup).eventRecorded leaks (control.execution.recall who) event =
          false
      · have member := onePacket_disclosure_offered covers trace who event turn unsent node
          material sends
        rw [decodedMember _ member, sends]
        have noOutput : ¬ ∃ message ∈ (application setup leaks).outputs
            (control.execution.recall who), message.payload.call.event? (graph setup) =
              some event := by
          intro named
          have recorded := (history_eventRecorded_iff rawTrace who event).mpr named
          rw [unsent] at recorded
          cases recorded
        constructor
        · intro silent
          cases silent
        · intro claim
          exact (claim ⟨transmits.symm, noOutput⟩).elim
      · have recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event =
            true := by
          cases value : (runtime setup).eventRecorded leaks (control.execution.recall who) event
          · exact (unsent value).elim
          · rfl
        obtain ⟨message, output, named⟩ := (history_eventRecorded_iff rawTrace who event).mp
          recorded
        have notMember : disclosure ∉ bounds.onePacketActions (runtime setup) leaks who
            (control.execution.recall who)
            (control.execution.observe (application setup leaks) who) := by
          intro member
          rcases ((bounds.mem_onePacketActions (runtime setup) leaks who _ _ disclosure).mp
              member).2 with silent | ⟨other, otherSends, permitted⟩
          · rw [sends] at silent
            cases silent
          rw [sends] at otherSends
          cases Option.some.inj otherSends
          have recalled := (runtime setup).countRecall_history leaks rawTrace
          have first := ((countPermits_eq_true_iff _ _).mp permitted).2.2
          rw [(runtime setup).localEnvelope_eq_of_recall leaks control.execution recalled.1
            recalled.2.1 who material] at first
          have earlier := earlierOwnPacket_of_output rawTrace who
            ((application setup leaks).packet ((application setup leaks).submit
              control.execution.application who material) who
              (control.execution.network.known who) material) message output
          apply first message earlier
          rw [named]
          rcases (runtime setup).canonicalServiceDecision_cases leaks who
              (control.execution.recall who)
              (control.execution.observe (application setup leaks) who) event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) with
            silent | submitted
          · have silent' : disclosure = ⟨none⟩ := silent
            rw [silent'] at sends
            cases sends
          · have submitted' : (runtime setup).submittedEvent? leaks disclosure = some event :=
              submitted
            unfold EventGraphRuntime.submittedEvent? at submitted'
            rw [sends] at submitted'
            exact submitted'.symm
        rw [decodedSilent _ notMember]
        constructor
        · intro _ both
          exact both.2 ⟨message, output, named⟩
        · intro _
          rfl

/-- **A disclosure that speaks opens the bound value.** Along every history of
the one-packet game, at a reveal of the player's turn, the chosen canonical
disclosure, when it transmits, opens the reveal's binding at its stored value
with the accepted handle. -/
theorem disclosure_opens {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId) {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (speaks : ((responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))).1.getD
          ⟨none⟩).transmission ≠ none) :
    OpensTurn event who control.execution
      ((responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))).1.getD ⟨none⟩) := by
  set disclosure := (runtime setup).canonicalServiceDecision leaks who
    (control.execution.recall who) (control.execution.observe (application setup leaks) who)
    event (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) with disclosureEq
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  by_cases member : disclosure ∈ bounds.onePacketActions (runtime setup) leaks who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)
  · have decoded : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) disclosure).1.getD ⟨none⟩ =
        disclosure := by
      simp only [responseChoice, member, ↓reduceDIte, Option.getD_some]
    rw [decoded] at speaks ⊢
    obtain ⟨material, sends⟩ := Option.ne_none_iff_exists'.mp speaks
    obtain ⟨handle, value, accepted, _, openable, shape⟩ :=
      disclosure_normal_form rawTrace who event node material sends
    have valid := bindingInvariant_of_history bounds horizon scheduler ⟨_, trace⟩ rfl
    have stored := valid.toAssociationInvariant.opening_stored binding handle value accepted
      openable
    refine ⟨payload, binding, checks, outputEq, codeEq, node, ?_⟩
    have shape' : disclosure = _ := shape
    rw [shape']
    exact ⟨_, handle, value, rfl, rfl, accepted, stored⟩
  · have decoded : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) disclosure).1.getD ⟨none⟩ =
        ⟨none⟩ := by
      simp only [responseChoice, member, ↓reduceDIte, Option.getD_some]
    rw [decoded] at speaks
    exact (speaks rfl).elim

/-- **A late option at a reveal is the disclosure.** Along every history of the
one-packet game, at a reveal of the player's turn, sending at any slot is the
chosen canonical disclosure. -/
theorem lateChoice_reveal (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    {slots : Nat} (slot : Fin slots) :
    lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who)) (some slot) =
      PMF.pure (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))) := by
  rw [lateChoice_some_eq_map (bounds := bounds) (initial := initialLaw setup) (horizon := horizon)
    (scheduler := scheduler) assessment who _ _ event turn slot]
  have constant : (asIfHonestProfile setup leaks assessment who
      (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))).map
      (slotChoiceOf setup leaks bounds (initialLaw setup) horizon scheduler who
        (control.execution.recall who) (control.execution.observe (application setup leaks) who)
        event slot.val) =
      (asIfHonestProfile setup leaks assessment who
        (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))).map
      (Function.const _ (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler
        who (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))
        ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
          (control.execution.observe (application setup leaks) who) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)))) := by
    apply map_congr_on_support
    intro choice supported
    change responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who _
      (slotResponse setup leaks who _ _ event slot.val choice) = _
    unfold slotResponse
    rw [onePacket_honest_discloses assessment trace who event turn outputEq choice supported]
    simp only [node, Function.const_apply]
  rw [constant, PMF.map_const]

/-- The part of a slot-trembled late component outside its uniform tier. -/
def lateCore (assessment : setup.intendedModel.BehavioralAssessment) (scale : ℝ)
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat}
    (options : PMF (LateOption slots)) (who : Player) (info : (application setup leaks).Info) :
    PMF ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      info) :=
  mix (scale ^ 2) (sq_nonneg _) (pow_le_one₀ nonnegative le_one)
    (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment who info)
    (mix scale nonnegative le_one
      (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who info))
      (options.bind (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler
        assessment who info)))

/-- Whether a one-packet choice keeps silence. -/
def choiceSilent {who : Player} {info : (application setup leaks).Info}
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      info) : Bool :=
  decide ((choice.1.getD ⟨none⟩).transmission = none)

omit [Fintype Player] in
/-- The silence law of a late component outside its uniform tier, given whether
the disclosure keeps silence. -/
def openingSilence (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat}
    (options : PMF (LateOption slots)) (disclosureSilent : Bool) : PMF Bool :=
  mix (scale ^ 2) (sq_nonneg _) (pow_le_one₀ nonnegative le_one) (PMF.pure disclosureSilent)
    (mix scale nonnegative le_one (PMF.pure true)
      (options.map fun option => option.isNone || disclosureSilent))

/-- **The silence of a late component at a reveal.** Along every history of the
one-packet game, at a reveal of the player's turn, the core of a late component
keeps silence with the law of its options and whether the disclosure keeps
silence. -/
theorem lateCore_silence {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat}
    (options : PMF (LateOption slots)) :
    (lateCore (bounds := bounds) (horizon := horizon) (scheduler := scheduler) assessment scale
        nonnegative le_one options who (some (control.execution.recall who,
          control.execution.observe (application setup leaks) who))).map choiceSilent =
      openingSilence scale nonnegative le_one options
        (choiceSilent (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (control.execution.recall who,
            control.execution.observe (application setup leaks) who))
          ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
            (control.execution.observe (application setup leaks) who) event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)))) := by
  have silenceFlag : choiceSilent (silenceChoice setup leaks bounds (initialLaw setup) horizon
      scheduler who (some (control.execution.recall who,
        control.execution.observe (application setup leaks) who))) = true := by
    unfold choiceSilent
    rw [silenceChoice_val who _ rfl]
    rfl
  unfold lateCore openingSilence
  rw [mix_map, mix_map, onePacket_slotChoice_reveal assessment trace who event turn node,
    PMF.pure_map, PMF.pure_map, silenceFlag, PMF.map_bind, ← PMF.bind_pure_comp]
  congr 2
  congr 1
  funext option
  cases option with
  | none =>
      rw [lateChoice_none, PMF.pure_map, silenceFlag]
      rfl
  | some slot =>
      rw [lateChoice_reveal assessment trace who event turn node slot, PMF.pure_map]
      rfl

omit [Fintype Player] in
/-- Protocol states with the same operational state give every player the same
own envelopes. -/
theorem outputs_congr {first second : (application setup leaks).Control}
    (same : operationalState setup leaks (some first) = operationalState setup leaks (some second))
    (who : Player) :
    (application setup leaks).outputs (first.execution.recall who) =
      (application setup leaks).outputs (second.execution.recall who) := by
  have recalled := congrArg LateKey.recalled (ofView_congr same who)
  simp only [LateKey.ofView] at recalled
  have emitted := congrArg (List.map Prod.snd) recalled
  simp only [List.map_map, Function.comp_def] at emitted
  have viaMap : ∀ entries : List (application setup leaks).PlayerEntry,
      entries.filterMap ReactiveApplication.PlayerEntry.emitted =
        (entries.map fun entry => entry.emitted).filterMap id := by
    intro entries
    rw [List.filterMap_map]
    rfl
  unfold ReactiveApplication.outputs
  rw [viaMap, viaMap, emitted]

/-- **Whether the disclosure keeps silence is read off the operational state.** -/
theorem disclosureSilent_congr (covers : bounds.CoversOutputValues) {remaining : Nat}
    {owner : Player}
    (firstHistory secondHistory : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    {first second : (application setup leaks).Execution}
    (firstCurrent : firstHistory.state = some ⟨remaining, some owner, first⟩)
    (secondCurrent : secondHistory.state = some ⟨remaining, some owner, second⟩)
    (same : operationalState setup leaks (some ⟨remaining, some owner, first⟩) =
      operationalState setup leaks (some ⟨remaining, some owner, second⟩))
    {event : (graph setup).EventId} (ready : first.application.config.cut.Ready event)
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    choiceSilent (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler owner
        (some (first.recall owner, first.observe (application setup leaks) owner))
        ((runtime setup).canonicalServiceDecision leaks owner (first.recall owner)
          (first.observe (application setup leaks) owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))) =
      choiceSilent (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler owner
        (some (second.recall owner, second.observe (application setup leaks) owner))
        ((runtime setup).canonicalServiceDecision leaks owner (second.recall owner)
          (second.observe (application setup leaks) owner) event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))) := by
  have ready' : second.application.config.cut.Ready event :=
    (SameOperational.ready same event).mp ready
  have actor := nodeView_resolve_actor outputEq codeEq
  have firstTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, first⟩) := firstCurrent ▸ firstHistory.trace
  have secondTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, second⟩) := secondCurrent ▸ secondHistory.trace
  have firstIff := disclosure_silent_iff covers firstTrace owner event
    (ownTurn?_of_ready setup _ ready actor) node
  have secondIff := disclosure_silent_iff covers secondTrace owner event
    (ownTurn?_of_ready setup _ ready' actor) node
  have packets := reactiveResolutionPacket_congr same ready node
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
  have outputs := outputs_congr same owner
  unfold choiceSilent
  rw [decide_eq_decide]
  refine firstIff.trans (Iff.trans ?_ secondIff.symm)
  change ¬ ((reactiveResolutionPacket owner event payload binding checks outputEq _
      (first.observe (application setup leaks) owner).application).isSome ∧ _) ↔
    ¬ ((reactiveResolutionPacket owner event payload binding checks outputEq _
      (second.observe (application setup leaks) owner).application).isSome ∧ _)
  rw [packets]
  change ¬ (_ ∧ ¬ ∃ message ∈ (application setup leaks).outputs (first.recall owner), _) ↔
    ¬ (_ ∧ ¬ ∃ message ∈ (application setup leaks).outputs (second.recall owner), _)
  rw [outputs]

variable (bounds horizon scheduler) in
open Classical in
/-- **The keyed silence law.** At a key deciding a publication event, the
silence law of the core of the late component at a representative state of a
one-packet history with the given operational state, the owner acting and the
event ready; silence when there is none. -/
def lateOpeningSilence (assessment : setup.intendedModel.BehavioralAssessment) (scale : ℝ)
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat}
    (options : LateKey setup leaks → PMF (LateOption slots)) (key : LateKey setup leaks)
    (image : Option (OperationalState setup leaks)) : PMF Bool :=
  match turnEvent key with
  | none => PMF.pure true
  | some event =>
      if represented : ∃ witness : (onePacketProtocol setup leaks bounds horizon
          scheduler).History × Nat × (application setup leaks).Execution,
          witness.1.state = some ⟨witness.2.1, some key.owner, witness.2.2⟩ ∧
          witness.2.2.application.config.cut.Ready event ∧
          operationalState setup leaks (some ⟨witness.2.1, some key.owner, witness.2.2⟩) =
            image then
        (lateCore (bounds := bounds) (horizon := horizon) (scheduler := scheduler) assessment
          scale nonnegative le_one (options (LateKey.ofView setup leaks key.owner
            (represented.choose.2.2.recall key.owner)
            (represented.choose.2.2.observe (application setup leaks) key.owner))) key.owner
          (some (represented.choose.2.2.recall key.owner,
            represented.choose.2.2.observe (application setup leaks) key.owner))).map
          choiceSilent
      else PMF.pure true

open Classical in
/-- **The owner's opening law for late components.** Suppose that at every
forced state of a one-packet history with the decided reveal ready and the owner
acting, the owner's policy is the slot-trembled component, with silence as its
alternative and the slot tier, of a mixture of late options chosen by the owner's
late-delivery key. When every publication value is a bounded value, the owner
keeps silence within the cube of the scale of the keyed silence law, and leaves
at most the cube of the scale outside silence and openings of the bound value. -/
theorem ownerOpeningLaw_of_lateComponents {LateOption' : Type}
    (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (options : LateKey setup leaks → LateOption' → LateKey setup leaks →
      PMF (LateOption slots))
    (key : LateKey setup leaks) (option : LateOption')
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {allowed : (application setup leaks).ProtocolState → Prop}
    (shape : ∀ event, PublicationTurn key event →
      ∀ (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
        (remaining : Nat) (execution : (application setup leaks).Execution),
        history.state = some ⟨remaining, some key.owner, execution⟩ →
        allowed history.state →
        ForcedState setup leaks key.owner history.state →
        execution.application.config.cut.Ready event →
        profile key.owner (some (execution.recall key.owner,
            execution.observe (application setup leaks) key.owner)) =
          slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
            nonnegative le_one key.owner (some (execution.recall key.owner,
              execution.observe (application setup leaks) key.owner))
            ((options key option (LateKey.ofView setup leaks key.owner
                (execution.recall key.owner)
                (execution.observe (application setup leaks) key.owner))).bind
              (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
                key.owner (some (execution.recall key.owner,
                  execution.observe (application setup leaks) key.owner))))
            (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup leaks) key.owner))))
            (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup leaks) key.owner)))) :
    OwnerOpeningLaw bounds horizon scheduler
      (fun key option => lateOpeningSilence bounds horizon scheduler assessment scale nonnegative
        le_one (options key option) key) key option profile (scale ^ 3) (scale ^ 3) allowed := by
  intro event turn history control current allowedState forced ready acting
  have turnEq := turnEvent_of_publicationTurn turn
  have turnCopy := turn
  rcases control with ⟨remaining, actor, execution⟩
  change actor = some key.owner at acting
  subst acting
  obtain ⟨_, payload, binding, checks, outputEq, codeEq, view⟩ := turn
  have trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some key.owner, execution⟩) := current ▸ history.trace
  have turnOwn : execution.application.publicView.ownTurn? key.owner = some event :=
    ownTurn?_of_ready setup _ ready (nodeView_resolve_actor outputEq codeEq)
  set info : (application setup leaks).Info := some (execution.recall key.owner,
    execution.observe (application setup leaks) key.owner) with infoEq
  set core := lateCore (bounds := bounds) (horizon := horizon) (scheduler := scheduler)
    assessment scale nonnegative le_one (options key option (LateKey.ofView setup leaks key.owner
      (execution.recall key.owner) (execution.observe (application setup leaks) key.owner)))
    key.owner info with coreEq
  have profileEq : profile key.owner info = mix (scale ^ 3) (pow_nonneg nonnegative 3)
      (pow_le_one₀ nonnegative le_one)
      ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup) horizon
        scheduler key.owner info) core := by
    rw [shape event turnCopy history remaining execution current
      (by rw [current]; exact allowedState) (by rw [current]; exact forced) ready]
    rfl
  have close := PMF.WithinTV.mix_right (scale ^ 3) (pow_nonneg nonnegative 3)
    (pow_le_one₀ nonnegative le_one)
    ((bounds.onePacketMenu (runtime setup) leaks).uniformPolicy (initialLaw setup) horizon
      scheduler key.owner info) core
  have represented : ∃ witness : (onePacketProtocol setup leaks bounds horizon
      scheduler).History × Nat × (application setup leaks).Execution,
      witness.1.state = some ⟨witness.2.1, some key.owner, witness.2.2⟩ ∧
      witness.2.2.application.config.cut.Ready event ∧
      operationalState setup leaks (some ⟨witness.2.1, some key.owner, witness.2.2⟩) =
        operationalState setup leaks (some ⟨remaining, some key.owner, execution⟩) :=
    ⟨(history, remaining, execution), current, ready, rfl⟩
  have silenceEq : lateOpeningSilence bounds horizon scheduler assessment scale nonnegative
      le_one (options key option) key
      (operationalState setup leaks (some ⟨remaining, some key.owner, execution⟩)) =
      core.map choiceSilent := by
    unfold lateOpeningSilence
    rw [turnEq]
    simp only
    rw [dite_eq_left represented]
    have spec := represented.choose_spec
    generalize represented.choose = witness at spec ⊢
    obtain ⟨chosenHistory, chosenRemaining, chosenExecution⟩ := witness
    obtain ⟨chosenCurrent, chosenReady, chosenSame⟩ := spec
    have remainingEq : chosenRemaining = remaining := SameOperational.remaining chosenSame
    subst remainingEq
    have chosenTrace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
        (some ⟨chosenRemaining, some key.owner, chosenExecution⟩) :=
      chosenCurrent ▸ chosenHistory.trace
    simp only
    rw [coreEq, infoEq,
      lateCore_silence chosenTrace assessment key.owner event
        (ownTurn?_of_ready setup _ chosenReady (nodeView_resolve_actor outputEq codeEq)) view
        scale nonnegative le_one _,
      lateCore_silence trace assessment key.owner event turnOwn view scale nonnegative le_one _,
      ofView_congr chosenSame key.owner,
      disclosureSilent_congr covers chosenHistory history chosenCurrent current chosenSame
        chosenReady view]
  rw [decodeProfile_eq_map]
  beta_reduce
  rw [profileEq, silenceEq, expect_map, expect_map, expect_map]
  constructor
  · have unit : ∀ choice, 0 ≤ ((fun action : (application setup leaks).Action =>
        if action.transmission = none then (1 : ℝ) else 0) ∘ fun choice :
          (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice
            key.owner info => choice.1.getD ⟨none⟩) choice ∧
        ((fun action : (application setup leaks).Action =>
          if action.transmission = none then (1 : ℝ) else 0) ∘ fun choice :
            (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice
              key.owner info => choice.1.getD ⟨none⟩) choice ≤ 1 := fun choice => by
      simp only [Function.comp]
      split <;> norm_num
    have flag : ((fun silent : Bool => if silent then (1 : ℝ) else 0) ∘ choiceSilent) =
        ((fun action : (application setup leaks).Action =>
          if action.transmission = none then (1 : ℝ) else 0) ∘ fun choice :
            (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice
              key.owner info => choice.1.getD ⟨none⟩) := by
      funext choice
      simp only [Function.comp, choiceSilent, decide_eq_true_eq]
    rw [flag]
    simpa only [mul_one] using close.abs_expect_sub_le_interval _ 0 1
      (fun point _ => by simpa only [zero_add] using unit point)
  · set rest : (application setup leaks).Action → ℝ := fun action =>
      if action.transmission = none ∨ OpensTurn event key.owner execution action then 0 else 1
      with restEq
    have unit : ∀ choice, 0 ≤ (rest ∘ fun choice :
          (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice
            key.owner info => choice.1.getD ⟨none⟩) choice ∧
        (rest ∘ fun choice :
          (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice
            key.owner info => choice.1.getD ⟨none⟩) choice ≤ 1 := fun choice => by
      simp only [Function.comp, restEq]
      split <;> norm_num
    have restDisclosure : rest ((responseChoice setup leaks bounds (initialLaw setup) horizon
        scheduler key.owner info ((runtime setup).canonicalServiceDecision leaks key.owner
          (execution.recall key.owner) (execution.observe (application setup leaks) key.owner)
          event (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))).1.getD
          ⟨none⟩) = 0 := by
      rw [restEq]
      beta_reduce
      by_cases silent : ((responseChoice setup leaks bounds (initialLaw setup) horizon scheduler
          key.owner info ((runtime setup).canonicalServiceDecision leaks key.owner
            (execution.recall key.owner) (execution.observe (application setup leaks) key.owner)
            event (cast (congrArg EventGraph.EventField.Action outputEq.symm) true))).1.getD
            ⟨none⟩).transmission = none
      · simp only [silent, true_or, ↓reduceIte]
      · split
        · rfl
        · rename_i neither
          exact (neither (Or.inr (disclosure_opens trace key.owner event view silent))).elim
    have restSilence : rest ((silenceChoice setup leaks bounds (initialLaw setup) horizon
        scheduler key.owner info).1.getD ⟨none⟩) = 0 := by
      rw [silenceChoice_val key.owner info rfl, Option.getD_some, restEq]
      simp only [true_or, ↓reduceIte]
    have mixSupport : ∀ {α : Type} {t : ℝ} {h0 : 0 ≤ t} {h1 : t ≤ 1} {μ ν : PMF α} {a : α},
        a ∈ (mix t h0 h1 μ ν).support → a ∈ μ.support ∨ a ∈ ν.support := by
      intro α t h0 h1 μ ν a member
      rw [PMF.mem_support_iff, mix_apply] at member
      by_contra neither
      rw [not_or, PMF.mem_support_iff, PMF.mem_support_iff, not_not, not_not] at neither
      rw [neither.1, neither.2, mul_zero, mul_zero, add_zero] at member
      exact member rfl
    have zero : expect core (rest ∘ fun choice :
        (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice
          key.owner info => choice.1.getD ⟨none⟩) = 0 := by
      rw [← expect_zero core]
      apply expect_congr_on_support
      intro choice member
      simp only [Function.comp]
      rw [coreEq] at member
      unfold lateCore at member
      rcases mixSupport member with slotted | inner
      · rw [onePacket_slotChoice_reveal assessment trace key.owner event turnOwn view,
          PMF.mem_support_pure_iff] at slotted
        rw [slotted]
        exact restDisclosure
      · rcases mixSupport inner with silent | main
        · rw [PMF.mem_support_pure_iff] at silent
          rw [silent]
          exact restSilence
        · obtain ⟨option, _, drawn⟩ := (PMF.mem_support_bind_iff _ _ _).mp main
          cases option with
          | none =>
              rw [lateChoice_none, PMF.mem_support_pure_iff] at drawn
              rw [drawn]
              exact restSilence
          | some slot =>
              rw [lateChoice_reveal assessment trace key.owner event turnOwn view slot,
                PMF.mem_support_pure_iff] at drawn
              rw [drawn]
              exact restDisclosure
    have near := close.abs_expect_sub_le_interval _ 0 1
      (fun point _ => by simpa only [zero_add] using unit point)
    simp only [mul_one] at near
    rw [zero, sub_zero] at near
    exact (abs_le.mp near).2

/-- **The owner plays keyed late components.** At every forced state of a
one-packet history with the key's decided event ready and the owner acting, the
owner's policy is the slot-trembled component, with silence as its alternative
and the slot tier, of a mixture of late options chosen by its late-delivery
key. -/
def LateComponentShape (assessment : setup.intendedModel.BehavioralAssessment) (scale : ℝ)
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat}
    (options : LateKey setup leaks → PMF (LateOption slots)) (key : LateKey setup leaks)
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    (allowed : (application setup leaks).ProtocolState → Prop := fun _ => True) : Prop :=
  ∀ event, (PublicationTurn key event ∨ ∃ payload, BindingTurn key event payload) →
    ∀ (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
      (remaining : Nat) (execution : (application setup leaks).Execution),
      history.state = some ⟨remaining, some key.owner, execution⟩ →
      allowed history.state →
      ForcedState setup leaks key.owner history.state →
      execution.application.config.cut.Ready event →
      profile key.owner (some (execution.recall key.owner,
          execution.observe (application setup leaks) key.owner)) =
        slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler scale
          nonnegative le_one key.owner (some (execution.recall key.owner,
            execution.observe (application setup leaks) key.owner))
          ((options (LateKey.ofView setup leaks key.owner (execution.recall key.owner)
              (execution.observe (application setup leaks) key.owner))).bind
            (lateChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup leaks) key.owner))))
          (PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
            key.owner (some (execution.recall key.owner,
              execution.observe (application setup leaks) key.owner))))
          (slotChoice setup leaks bounds (initialLaw setup) horizon scheduler assessment
            key.owner (some (execution.recall key.owner,
              execution.observe (application setup leaks) key.owner)))

end Vegas
