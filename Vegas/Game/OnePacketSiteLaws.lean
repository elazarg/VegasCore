/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketRecordedSilence

/-! # The owner's laws for the certificate's components at a late site

Along play from a late-delivery site, the owner's later activations at the
decided event follow its late component while it has not sent for the event,
and its prescribed component once it has (`Vegas.SiteComponentShape`). Once it
has sent, every part of the prescribed component keeps silence, and so does the
keyed law (`Vegas.lateMoves_of_silent`). So the owner's binding and opening
laws hold at every allowed state (`Vegas.ownerBindingLaw_of_siteComponents`,
`Vegas.ownerOpeningLaw_of_siteComponents`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A point of a mixture lies in the support of one of its parts. -/
theorem mem_support_mix_cases {α : Type} {t : ℝ} {h0 : 0 ≤ t} {h1 : t ≤ 1} {μ ν : PMF α}
    {a : α} (member : a ∈ (mix t h0 h1 μ ν).support) : a ∈ μ.support ∨ a ∈ ν.support := by
  rw [PMF.mem_support_iff, mix_apply] at member
  by_contra neither
  rw [not_or, PMF.mem_support_iff, PMF.mem_support_iff, not_not, not_not] at neither
  rw [neither.1, neither.2, mul_zero, mul_zero, add_zero] at member
  exact member rfl

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **The owner's components at a late site.** At every allowed forced state of a
one-packet history with the key's decided event ready and the owner acting, the
owner plays the slot-trembled late component of a mixture of late options chosen
by its late-delivery key while it has not sent for the event; once it has, it
plays a slot-trembled component whose main part is the as-if-honest choice, as
the prescribed component does, or a mixture of late options. -/
def SiteComponentShape (assessment : setup.intendedModel.BehavioralAssessment) (scale : ℝ)
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat}
    (options : LateKey setup runtime leaks → PMF (LateOption slots)) (key : LateKey setup runtime
      leaks)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (allowed : (application setup runtime leaks).ProtocolState → Prop) : Prop :=
  ∀ event, (PublicationTurn (runtime := runtime) key event ∨ ∃ payload, BindingTurn (runtime :=
    runtime) key event payload) →
    ∀ (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
      (remaining : Nat) (execution : (application setup runtime leaks).Execution),
      history.state = some ⟨remaining, some key.owner, execution⟩ →
      allowed history.state →
      ForcedState setup runtime leaks key.owner history.state →
      execution.application.config.cut.Ready event →
      (runtime.eventRecorded leaks (execution.recall key.owner) event = false →
        profile key.owner (some (execution.recall key.owner,
            execution.observe (application setup runtime leaks) key.owner)) =
          slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler scale
            nonnegative le_one key.owner (some (execution.recall key.owner,
              execution.observe (application setup runtime leaks) key.owner))
            ((options (LateKey.ofView setup runtime leaks key.owner
              (execution.recall key.owner)
                (execution.observe (application setup runtime leaks) key.owner))).bind
              (lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment
                key.owner (some (execution.recall key.owner,
                  execution.observe (application setup runtime leaks) key.owner))))
            (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner))))
            (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner)))) ∧
      (runtime.eventRecorded leaks (execution.recall key.owner) event = true →
        ∃ main : PMF ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
            scheduler).Choice key.owner (some (execution.recall key.owner,
              execution.observe (application setup runtime leaks) key.owner))),
          (main = honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
              assessment key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner)) ∨
            ∃ others : PMF (LateOption slots), main = others.bind
              (lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment
                key.owner (some (execution.recall key.owner,
                  execution.observe (application setup runtime leaks) key.owner)))) ∧
          profile key.owner (some (execution.recall key.owner,
              execution.observe (application setup runtime leaks) key.owner)) =
            slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler scale
              nonnegative le_one key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner)) main
              (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon
                scheduler
                key.owner (some (execution.recall key.owner,
                  execution.observe (application setup runtime leaks) key.owner))))
              (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment
                key.owner (some (execution.recall key.owner,
                  execution.observe (application setup runtime leaks) key.owner))))

omit [Fintype Player] in
/-- A key decides one event: the owner's turn. -/
theorem turn_unique {key : LateKey setup runtime leaks} {first second : (graph setup).EventId}
    (firstTurn : PublicationTurn (runtime := runtime) key first ∨ ∃ payload, BindingTurn (runtime
      := runtime) key first payload)
    (secondTurn : PublicationTurn (runtime := runtime) key second ∨ ∃ payload, BindingTurn
      (runtime := runtime) key second payload) :
    first = second := by
  have own : ∀ {event}, (PublicationTurn (runtime := runtime) key event ∨ ∃ payload, BindingTurn
    (runtime := runtime) key event payload) →
      key.current.1.ownTurn? key.owner = some event := by
    intro event turn
    rcases turn with published | ⟨_, bound⟩
    · exact published.1
    · exact bound.1
  exact Option.some.inj ((own firstTurn).symm.trans (own secondTurn))

/-- The states at which the owner has not sent for the key's decided event. -/
def OwnerUnsent (key : LateKey setup runtime leaks) : (application setup runtime
  leaks).ProtocolState → Prop
  | none => True
  | some control => ∀ event, (PublicationTurn (runtime := runtime) key event ∨ ∃ payload,
    BindingTurn (runtime := runtime) key event
      payload) → runtime.eventRecorded leaks (control.execution.recall key.owner) event =
        false

/-- **The site shape restricted to unsent states is the late shape.** -/
theorem lateComponentShape_of_site (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat}
    (options : LateKey setup runtime leaks → PMF (LateOption slots)) (key : LateKey setup runtime
      leaks)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (allowed : (application setup runtime leaks).ProtocolState → Prop)
    (shape : SiteComponentShape (runtime := runtime) assessment scale nonnegative le_one options
      key profile
      allowed) :
    LateComponentShape (runtime := runtime) assessment scale nonnegative le_one options key profile
      (fun state => allowed state ∧ OwnerUnsent (runtime := runtime) key state) := by
  intro event turn history remaining execution current allowedState forced ready
  have unsent := allowedState.2
  rw [current] at unsent
  exact (shape event turn history remaining execution current allowedState.1 forced ready).1
    (unsent event turn)

/-- Once the owner has sent for an event, the count verdict permits no slot of
it, so every slot moves to silence. -/
theorem slotMove_of_recorded {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (recorded : runtime.eventRecorded leaks (control.execution.recall who) event = true)
    (slot : Nat) :
    slotMove (runtime := runtime) control.execution who event slot = none := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have recalled := runtime.countRecall_history leaks rawTrace
  obtain ⟨message, output, named⟩ := (history_eventRecorded_iff (runtime := runtime) rawTrace who
    event).mp recorded
  unfold slotMove
  split
  · rename_i permitted
    exfalso
    have first := ((countPermits_eq_true_iff _ _).mp permitted).2.2
    obtain ⟨inOutputs, owner, lower⟩ := earlierOwnPacket_of_output rawTrace who
      (slotEnvelope setup runtime leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who) event slot).payload
      message output
    apply first message ⟨inOutputs, owner, ?_⟩
    · rw [named]
      rfl
    · change message.id.2 < (application setup runtime leaks).submissionCount
        (control.execution.recall who)
      rw [← recalled.2.1 who]
      exact lower
  · rfl

omit [Fintype Player] in
/-- The keyed law of moves when every slot moves to silence. -/
theorem lateMoves_of_silent (execution : (application setup runtime leaks).Execution) (who : Player)
    (event : (graph setup).EventId) (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {slots : Nat} (options : PMF (LateOption slots))
    (silent : ∀ slot, slotMove (runtime := runtime) execution who event slot = none) :
    lateMoves (runtime := runtime) (bounds := bounds) execution who event scale nonnegative le_one
      options =
      PMF.pure none := by
  unfold lateMoves
  have slotConst : slotMove (runtime := runtime) execution who event = Function.const _ none :=
    funext silent
  have optionConst : (fun option : LateOption slots => option.elim none fun slot =>
      slotMove (runtime := runtime) execution who event slot.val) = Function.const _ none := by
    funext option
    cases option <;> simp [silent]
  rw [optionConst, slotConst, PMF.map_const, PMF.map_const, mix_self, mix_self]

/-- At a state of a one-packet history whose owner has sent for an event, every
choice of a component's core keeps silence when its main part is the as-if-honest
choice or a mixture of late options. -/
theorem core_silent (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (recorded : runtime.eventRecorded leaks (control.execution.recall who) event = true)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat}
    (main : PMF ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).Choice
      who (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who))))
    (mainCases : main = honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
        assessment who (some (control.execution.recall who,
          control.execution.observe (application setup runtime leaks) who)) ∨
      ∃ others : PMF (LateOption slots), main = others.bind
        (lateChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who
          (some (control.execution.recall who,
            control.execution.observe (application setup runtime leaks) who)))) :
    ∀ choice ∈ (mix (scale ^ 2) (sq_nonneg _) (pow_le_one₀ nonnegative le_one)
        (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment who
          (some (control.execution.recall who,
            control.execution.observe (application setup runtime leaks) who)))
        (mix scale nonnegative le_one
          (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
            who
            (some (control.execution.recall who,
              control.execution.observe (application setup runtime leaks) who))))
          main)).support,
      choice.1.getD ⟨none⟩ = ⟨none⟩ := by
  obtain ⟨honest, slot, late, silence⟩ :=
    parts_silent_of_recorded (runtime := runtime) assessment trace who event turn recorded
  intro choice member
  rcases mem_support_mix_cases member with slotted | inner
  · exact slot choice slotted
  · rcases mem_support_mix_cases inner with silent | mainly
    · rw [PMF.mem_support_pure_iff] at silent
      rw [silent]
      exact silence
    · rcases mainCases with rfl | ⟨others, rfl⟩
      · exact honest choice mainly
      · obtain ⟨option, _, drawn⟩ := (PMF.mem_support_bind_iff _ _ _).mp mainly
        exact late option choice drawn

/-- At a state of a one-packet history whose owner has sent for an event, every
choice the late component's core can make keeps silence. -/
theorem lateCore_silent (assessment : setup.intendedModel.BehavioralAssessment)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? who = some event)
    (recorded : runtime.eventRecorded leaks (control.execution.recall who) event = true)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat}
    (options : PMF (LateOption slots)) :
    ∀ choice ∈ (lateCore (runtime := runtime) (bounds := bounds) (horizon := horizon) (scheduler
      := scheduler)
        assessment scale nonnegative le_one options who (some (control.execution.recall who,
          control.execution.observe (application setup runtime leaks) who))).support,
      choice.1.getD ⟨none⟩ = ⟨none⟩ := by
  obtain ⟨_, slot, late, silence⟩ :=
    parts_silent_of_recorded (runtime := runtime) assessment trace who event turn recorded
  intro choice member
  unfold lateCore at member
  rcases mem_support_mix_cases member with slotted | inner
  · exact slot choice slotted
  · rcases mem_support_mix_cases inner with silent | main
    · rw [PMF.mem_support_pure_iff] at silent
      rw [silent]
      exact silence
    · obtain ⟨option, _, drawn⟩ := (PMF.mem_support_bind_iff _ _ _).mp main
      exact late option choice drawn

/-- Recorded at one state of a one-packet history, recorded at every state with
the same operational state. -/
theorem recorded_congr {remaining : Nat} {actor : Option Player}
    (firstHistory secondHistory : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History)
    {first second : (application setup runtime leaks).Execution}
    (firstCurrent : firstHistory.state = some ⟨remaining, actor, first⟩)
    (secondCurrent : secondHistory.state = some ⟨remaining, actor, second⟩)
    (same : operationalState setup runtime leaks (some ⟨remaining, actor, first⟩) =
      operationalState setup runtime leaks (some ⟨remaining, actor, second⟩))
    (who : Player) (event : (graph setup).EventId) :
    runtime.eventRecorded leaks (first.recall who) event =
      runtime.eventRecorded leaks (second.recall who) event := by
  have firstRaw : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some ⟨remaining, actor, first⟩) :=
    firstCurrent ▸ (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon scheduler firstHistory.trace
  have secondRaw : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some ⟨remaining, actor, second⟩) :=
    secondCurrent ▸ (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon scheduler secondHistory.trace
  have outputs := outputs_congr (runtime := runtime) same who
  apply Bool.eq_iff_iff.mpr
  rw [history_eventRecorded_iff (runtime := runtime) firstRaw who event, history_eventRecorded_iff
    (runtime := runtime) secondRaw who event]
  change (∃ message ∈ (application setup runtime leaks).outputs (first.recall who), _) ↔
    (∃ message ∈ (application setup runtime leaks).outputs (second.recall who), _)
  rw [outputs]

/-- **The owner's binding law for the certificate's components.** -/
theorem ownerBindingLaw_of_siteComponents {LateOption' : Type}
    (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    {slots : Nat} (slotsLe : slots ≤ bounds.candidateCount)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (options : LateKey setup runtime leaks → LateOption' → LateKey setup runtime leaks →
      PMF (LateOption slots))
    (key : LateKey setup runtime leaks) (option : LateOption')
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (allowed : (application setup runtime leaks).ProtocolState → Prop)
    (shape : SiteComponentShape (runtime := runtime) assessment scale nonnegative le_one (options
      key option) key
      profile allowed) :
    OwnerBindingLaw (runtime := runtime) bounds horizon scheduler
      (fun key option => lateBindingMoves (runtime := runtime) bounds horizon scheduler scale
        nonnegative le_one
        (options key option) key) key option profile (scale ^ 3) allowed := by
  intro event payload turn history remaining execution current allowedState forced ready
  have turnBoth : PublicationTurn (runtime := runtime) key event ∨ ∃ payload, BindingTurn (runtime
    := runtime) key event payload :=
    Or.inr ⟨payload, turn⟩
  by_cases recorded : runtime.eventRecorded leaks (execution.recall key.owner) event =
      true
  · have decided := bindingTurn_of_bindingTurn (runtime := runtime) turn
    obtain ⟨_, ⟨outputEq, codeEq, node⟩, _⟩ := turn
    have trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
        (some ⟨remaining, some key.owner, execution⟩) := current ▸
          history.trace
    have turnOwn : execution.application.publicView.ownTurn? key.owner = some
      event :=
      ownTurn?_of_ready setup _ ready (nodeView_bind_actor outputEq codeEq)
    obtain ⟨main, mainCases, profileEq⟩ :=
      (shape event turnBoth history remaining execution current allowedState forced ready).2
        recorded
    have silent := core_silent (runtime := runtime) assessment trace key.owner event turnOwn
      recorded scale
      nonnegative le_one main mainCases
    rw [decodeProfile_eq_map, PMF.map_comp, profileEq]
    unfold slotTrembledChoice
    rw [mix_map]
    have coreEq : PMF.map (commitMove (runtime := runtime) event key.owner
      payload execution ∘
        fun choice : (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
          scheduler).Choice key.owner (some (execution.recall key.owner,
            execution.observe (application setup runtime leaks) key.owner))
              => choice.1.getD ⟨none⟩)
        (mix (scale ^ 2) (sq_nonneg _) (pow_le_one₀ nonnegative le_one)
          (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment
            key.owner (some (execution.recall key.owner,
              execution.observe (application setup runtime leaks) key.owner)))
          (mix scale nonnegative le_one
            (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner)))) main)) =
        PMF.pure (some none) := by
      rw [map_congr_on_support (g := Function.const _ (some none)) _ fun choice supported => by
        simp only [Function.comp, silent choice supported]
        exact commitMove_silent (runtime := runtime) execution]
      exact PMF.map_const _ _
    have represented : ∃ witness : (onePacketProtocol setup runtime leaks bounds horizon
        scheduler).History × Nat × (application setup runtime leaks).Execution,
        witness.1.state = some ⟨witness.2.1, some key.owner, witness.2.2⟩ ∧
        (operationalState setup runtime leaks (some ⟨witness.2.1, some key.owner, witness.2.2⟩),
          commitStatuses (runtime := runtime) event key.owner payload
            witness.2.2.application
            witness.2.2.network.pending) =
        (operationalState setup runtime leaks (some ⟨remaining, some key.owner, execution⟩),
          commitStatuses (runtime := runtime) event key.owner payload
            execution.application
            execution.network.pending) :=
      ⟨(history, remaining, execution), current, rfl⟩
    have movesEq : lateBindingMoves (runtime := runtime) bounds horizon scheduler scale
      nonnegative le_one
        (options key option) key
        (operationalState setup runtime leaks (some ⟨remaining, some key.owner, execution⟩),
          commitStatuses (runtime := runtime) event key.owner payload
            execution.application
            execution.network.pending) = PMF.pure none := by
      unfold lateBindingMoves
      rw [decided]
      simp only
      rw [dite_eq_left represented]
      have spec := represented.choose_spec
      generalize represented.choose = witness at spec ⊢
      obtain ⟨chosenHistory, chosenRemaining, chosenExecution⟩ := witness
      obtain ⟨chosenCurrent, chosenImage⟩ := spec
      have same := (Prod.mk.inj chosenImage).1
      have remainingEq : chosenRemaining = remaining := SameOperational.remaining same
      subst remainingEq
      have chosenTrace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
          (some ⟨chosenRemaining, some key.owner, chosenExecution⟩) :=
        chosenCurrent ▸ chosenHistory.trace
      have chosenRecorded : runtime.eventRecorded leaks
          (chosenExecution.recall key.owner) event = true := by
        rw [recorded_congr (runtime := runtime) chosenHistory history chosenCurrent current same
          key.owner event]
        exact recorded
      exact lateMoves_of_silent (runtime := runtime) _ _ _ _ _ _ _
        (slotMove_of_recorded (runtime := runtime) chosenTrace key.owner
          event chosenRecorded)
    beta_reduce
    rw [coreEq, movesEq, PMF.pure_map]
    exact PMF.WithinTV.mix_right _ _ _ _ _
  · have unsent : runtime.eventRecorded leaks (execution.recall key.owner)
      event =
        false := by
      cases value : runtime.eventRecorded leaks (execution.recall key.owner)
        event
      · rfl
      · exact (recorded value).elim
    have lateShape := lateComponentShape_of_site (runtime := runtime) assessment scale nonnegative
      le_one
      (options key option) key profile allowed shape
    have law := ownerBindingLaw_of_lateComponents (runtime := runtime) assessment covers capacity
      slotsLe scale
      nonnegative le_one options key option profile
      (allowed := fun state => allowed state ∧ OwnerUnsent (runtime := runtime) key state)
      fun event payload turn => lateShape event (Or.inr ⟨payload, turn⟩)
    refine law event payload turn history remaining execution current ⟨allowedState, ?_⟩ forced
      ready
    rw [current]
    intro other otherTurn
    rw [turn_unique (runtime := runtime) otherTurn turnBoth]
    exact unsent

open Classical in
/-- **The owner's opening law for the certificate's components.** -/
theorem ownerOpeningLaw_of_siteComponents {LateOption' : Type}
    (assessment : setup.intendedModel.BehavioralAssessment)
    (covers : bounds.CoversOutputValues) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (options : LateKey setup runtime leaks → LateOption' → LateKey setup runtime leaks →
      PMF (LateOption slots))
    (key : LateKey setup runtime leaks) (option : LateOption')
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (allowed : (application setup runtime leaks).ProtocolState → Prop)
    (shape : SiteComponentShape (runtime := runtime) assessment scale nonnegative le_one (options
      key option) key
      profile allowed) :
    OwnerOpeningLaw (runtime := runtime) bounds horizon scheduler
      (fun key option => lateOpeningSilence (runtime := runtime) bounds horizon scheduler
        assessment scale nonnegative
        le_one (options key option) key) key option profile (scale ^ 3) (scale ^ 3) allowed := by
  intro event turn history control current allowedState forced ready acting
  have turnBoth : PublicationTurn (runtime := runtime) key event ∨ ∃ payload, BindingTurn (runtime
    := runtime) key event payload :=
    Or.inl turn
  have turnEq := turnEvent_of_publicationTurn (runtime := runtime) turn
  rcases control with ⟨remaining, actor, execution⟩
  change actor = some key.owner at acting
  subst acting
  by_cases recorded : runtime.eventRecorded leaks (execution.recall key.owner) event =
      true
  · obtain ⟨_, payload, binding, checks, outputEq, codeEq, view⟩ := turn
    have trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
        (some ⟨remaining, some key.owner, execution⟩) := current ▸
          history.trace
    have turnOwn : execution.application.publicView.ownTurn? key.owner = some
      event :=
      ownTurn?_of_ready setup _ ready (nodeView_resolve_actor outputEq codeEq)
    obtain ⟨main, mainCases, profileEq⟩ :=
      (shape event turnBoth history remaining execution current
        (by rw [current]; exact allowedState) (by rw [current]; exact forced) ready).2 recorded
    have silent := core_silent (runtime := runtime) assessment trace key.owner event turnOwn
      recorded scale
      nonnegative le_one main mainCases
    have represented : ∃ witness : (onePacketProtocol setup runtime leaks bounds horizon
        scheduler).History × Nat × (application setup runtime leaks).Execution,
        witness.1.state = some ⟨witness.2.1, some key.owner, witness.2.2⟩ ∧
        witness.2.2.application.config.cut.Ready event ∧
        operationalState setup runtime leaks (some ⟨witness.2.1, some key.owner, witness.2.2⟩) =
          operationalState setup runtime leaks (some ⟨remaining, some key.owner, execution⟩) :=
      ⟨(history, remaining, execution), current, ready, rfl⟩
    have silenceEq : lateOpeningSilence (runtime := runtime) bounds horizon scheduler assessment
      scale nonnegative
        le_one (options key option) key
        (operationalState setup runtime leaks (some ⟨remaining, some key.owner, execution⟩)) =
        PMF.pure true := by
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
      have chosenTrace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace
          (some ⟨chosenRemaining, some key.owner, chosenExecution⟩) :=
        chosenCurrent ▸ chosenHistory.trace
      have chosenRecorded : runtime.eventRecorded leaks
          (chosenExecution.recall key.owner) event = true := by
        rw [recorded_congr (runtime := runtime) chosenHistory history chosenCurrent current
          chosenSame key.owner
          event]
        exact recorded
      have chosenSilent := lateCore_silent (runtime := runtime) (bounds := bounds) (horizon :=
        horizon)
        (scheduler := scheduler) assessment chosenTrace key.owner event
        (ownTurn?_of_ready setup _ chosenReady (nodeView_resolve_actor outputEq codeEq))
        chosenRecorded scale nonnegative le_one (options key option (LateKey.ofView setup runtime
          leaks
          key.owner (chosenExecution.recall key.owner)
          (chosenExecution.observe (application setup runtime leaks) key.owner)))
      simp only
      rw [map_congr_on_support (g := Function.const _ true) _ fun choice supported => by
        simp only [choiceSilent, chosenSilent choice supported, Function.const_apply,
          decide_true]]
      exact PMF.map_const _ _
    beta_reduce
    rw [silenceEq, expect_pure, decodeProfile_eq_map, profileEq]
    unfold slotTrembledChoice
    rw [expect_map, expect_map]
    set core := mix (scale ^ 2) (sq_nonneg _) (pow_le_one₀ nonnegative le_one)
      (slotChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler assessment
        key.owner
        (some (execution.recall key.owner,
          execution.observe (application setup runtime leaks) key.owner)))
      (mix scale nonnegative le_one
        (PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
          key.owner (some (execution.recall key.owner,
            execution.observe (application setup runtime leaks) key.owner))))
              main) with coreEq
    have close := PMF.WithinTV.mix_right (scale ^ 3) (pow_nonneg nonnegative 3)
      (pow_le_one₀ nonnegative le_one)
      ((bounds.onePacketMenu runtime leaks).uniformPolicy (initialLaw setup) horizon
        scheduler key.owner (some (execution.recall key.owner,
          execution.observe (application setup runtime leaks) key.owner))) core
    constructor
    · have unit : ∀ choice, 0 ≤ ((fun action : (application setup runtime leaks).Action =>
          if action.transmission = none then (1 : ℝ) else 0) ∘ fun choice :
            (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler).Choice
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner)) =>
            choice.1.getD ⟨none⟩) choice ∧
          ((fun action : (application setup runtime leaks).Action =>
            if action.transmission = none then (1 : ℝ) else 0) ∘ fun choice :
              (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
                scheduler).Choice
                key.owner (some (execution.recall key.owner,
                  execution.observe (application setup runtime leaks) key.owner)) =>
              choice.1.getD ⟨none⟩) choice ≤ 1 := fun choice => by
        simp only [Function.comp]
        split <;> norm_num
      have coreOne : expect core ((fun action : (application setup runtime leaks).Action =>
          if action.transmission = none then (1 : ℝ) else 0) ∘ fun choice :
            (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler).Choice
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner)) =>
            choice.1.getD ⟨none⟩) = 1 := by
        rw [expect_congr_on_support (g := fun _ => (1 : ℝ)) fun choice supported => by
          simp only [Function.comp, silent choice supported, ↓reduceIte]]
        exact expect_constant core 1
      have near := close.abs_expect_sub_le_interval _ 0 1
        (fun point _ => by simpa only [zero_add] using unit point)
      simp only [mul_one] at near
      rw [coreOne] at near
      simpa only [↓reduceIte] using near
    · set rest : (application setup runtime leaks).Action → ℝ := fun action =>
        if action.transmission = none ∨ OpensTurn (runtime := runtime) event key.owner
          execution action then 0 else 1
        with restEq
      have unit : ∀ choice, 0 ≤ (rest ∘ fun choice :
            (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler).Choice
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner)) =>
            choice.1.getD ⟨none⟩) choice ∧
          (rest ∘ fun choice :
            (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler).Choice
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner)) =>
            choice.1.getD ⟨none⟩) choice ≤ 1 := fun choice => by
        simp only [Function.comp, restEq]
        split <;> norm_num
      have coreZero : expect core (rest ∘ fun choice :
            (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler).Choice
              key.owner (some (execution.recall key.owner,
                execution.observe (application setup runtime leaks) key.owner)) =>
            choice.1.getD ⟨none⟩) = 0 := by
        rw [expect_congr_on_support (g := fun _ => (0 : ℝ)) fun choice supported => by
          simp only [Function.comp, silent choice supported, restEq, true_or, ↓reduceIte]]
        exact expect_zero core
      have near := close.abs_expect_sub_le_interval _ 0 1
        (fun point _ => by simpa only [zero_add] using unit point)
      simp only [mul_one] at near
      rw [coreZero, sub_zero] at near
      exact (abs_le.mp near).2
  · have unsent : runtime.eventRecorded leaks (execution.recall key.owner)
      event =
        false := by
      cases value : runtime.eventRecorded leaks (execution.recall key.owner)
        event
      · rfl
      · exact (recorded value).elim
    have lateShape := lateComponentShape_of_site (runtime := runtime) assessment scale nonnegative
      le_one
      (options key option) key profile allowed shape
    have law := ownerOpeningLaw_of_lateComponents (runtime := runtime) assessment covers scale
      nonnegative le_one
      options key option profile (allowed := fun state => allowed state ∧ OwnerUnsent (runtime :=
        runtime) key state)
      fun event turn => lateShape event (Or.inl turn)
    refine law event turn history _ current ⟨allowedState, ?_⟩ forced ready rfl
    intro other otherTurn
    rw [turn_unique (runtime := runtime) otherTurn turnBoth]
    exact unsent

end Vegas
