/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBaseAssembly
import Vegas.Game.OnePacketSlotLawDischarge
import Vegas.Game.OnePacketRelevantLumping

/-! # The native comparison profile's keyed failure kernel -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- The options of the certificate's lumping at a late key: the installed option
at the key, and the key's weights at every other key. -/
def certificateOptions {slots : Nat}
    (weights : ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (key : LateKey setup timeouts leaks) (option : LateOption slots) (other : LateKey setup timeouts
      leaks) :
    PMF (LateOption slots) :=
  if other = key then PMF.pure option
  else keyWeights setup timeouts leaks bounds horizon scheduler weights (some other)

omit [Finite setup.intendedProtocol.History] in
/-- **The certificate's components at forced decisions.** At a history in a
forced state of `who` acting at a decision with an event ready that `who` was
activated for, a profile assembled from the certificate's components plays the
late component of the key's weights while `who` has not sent for the event, and
the slot-trembled prescribed component once it has. -/
theorem certificate_strategyShape (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence) (n : ℕ) (who : Player)
    (history : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).History)
    (remaining : Nat) (execution : (application setup timeouts leaks).Execution)
    (event : (graph setup).EventId)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (forcedState : ForcedState setup timeouts leaks who history.state)
    (ready : execution.application.config.cut.Ready event)
    (activated : ∃ entry ∈ execution.logs who, ActivatedAt setup timeouts leaks who event entry) :
    ((eventRecorded timeouts) leaks (execution.logs who) event = false →
      (targetSequence n).strategy who
          (some (execution.logs who, execution.observe (application setup timeouts leaks) who)) =
        slotTrembledChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
          (scale n)
          (scale_pos n).le (scale_le_one n) who
          (some (execution.logs who, execution.observe (application setup timeouts leaks) who))
          ((keyWeights setup timeouts leaks bounds horizon scheduler (weights n)
              (some (LateKey.ofView setup timeouts leaks who (execution.logs who)
                (execution.observe (application setup timeouts leaks) who)))).bind
            (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler (sequence
              n) who
              (some (execution.logs who, execution.observe (application setup timeouts leaks)
                who))))
          (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            who
            (some (execution.logs who, execution.observe (application setup timeouts leaks) who))))
          (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler (sequence n)
            who
            (some (execution.logs who, execution.observe (application setup timeouts leaks)
              who)))) ∧
    ((eventRecorded timeouts) leaks (execution.logs who) event = true →
      ∃ main : PMF ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler).Choice who (some (execution.logs who,
            execution.observe (application setup timeouts leaks) who))),
        (main = honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            (sequence n) who (some (execution.logs who,
              execution.observe (application setup timeouts leaks) who)) ∨
          ∃ others : PMF (LateOption slots), main = others.bind
            (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler (sequence
              n) who
              (some (execution.logs who,
                execution.observe (application setup timeouts leaks) who)))) ∧
        (targetSequence n).strategy who (some (execution.logs who,
            execution.observe (application setup timeouts leaks) who)) =
          slotTrembledChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
            (scale n)
            (scale_pos n).le (scale_le_one n) who (some (execution.logs who,
              execution.observe (application setup timeouts leaks) who)) main
            (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon
              scheduler
              who (some (execution.logs who,
                execution.observe (application setup timeouts leaks) who))))
            (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler (sequence
              n) who
              (some (execution.logs who,
                execution.observe (application setup timeouts leaks) who)))) := by
  have observed : (onePacketN).infoOf who history.trace =
      some (execution.logs who, execution.observe (application setup timeouts leaks) who) := by
    refine ((bounds.onePacketMenu timeouts leaks).info (initialLaw setup) horizon
      scheduler who history.trace).trans ?_
    rw [current]
    simp [ReactiveApplication.observe]
  have running : ¬ (onePacketProtocol setup timeouts leaks bounds horizon scheduler).terminal
      history.state := by
    rw [current]
    rintro ⟨_, actorNone⟩
    cases actorNone
  have played := (onePacketN).mem_playedInformation (who := who) running
  rw [observed] at played
  have forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
    setup)
      horizon scheduler who (some (execution.logs who,
        execution.observe (application setup timeouts leaks) who)) :=
    observed ▸ forcedAgent_of_history (timeouts := timeouts) history forcedState
  let agent : (onePacketN).InformationAgent (onePacketN).playedInformation :=
    ⟨who, ⟨_, played⟩⟩
  have readyOwned : (graph setup).actor? event = some who := by
    obtain ⟨entry, _member, recalled⟩ := activated
    exact (PublicView.ownTurn?_spec _ who event recalled).2
  have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
    scheduler (current ▸ history.trace)
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have active := execution.application.active_of_ready_owned facts.quiescent ready readyOwned
  obtain ⟨rank, point, ordered, decoded, forcedPoint⟩ := current ▸ forcedState
  have clear := defaulted_eq_empty_of_decodedForced
    ((decodedPoint_eq_of_isPrefix ordered).trans decoded) forcedPoint active
  have notFree : ¬ FreeAgent setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler agent :=
    fun unforced => unforced ⟨⟨_, _, rfl, clear⟩, forced⟩
  have atAgent := (onePacketN).agentBehavior_at (onePacketN).playedInformation
    (onePacketFallback setup timeouts leaks bounds horizon scheduler)
    (fun agent => (weights n (onePacketPool setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler
      agent)).bind
      (freeKeyedComponent
        (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos
          scale_le_one n)
        (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one n)
        (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one (slots := slots) n) agent)) agent
  obtain ⟨entry, member, activatedAt⟩ := activated
  have owned : (graph setup).actor? event = some who :=
    (PublicView.ownTurn?_spec _ who event activatedAt).2
  have turn : execution.application.publicView.ownTurn? who = some event :=
    ownTurn?_of_ready setup execution.application ready owned
  constructor
  · intro unrecorded
    have late : LateDelivery setup timeouts leaks who (some (execution.logs who,
        execution.observe (application setup timeouts leaks) who)) :=
      ⟨_, _, event, rfl, pendingEvent_of_spec (timeouts := timeouts) turn unrecorded, entry, member,
        activatedAt⟩
    have keyed : ownedKeyed (FreeAgent setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler)
        (LateDeliveryAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler)
          agent :=
      ⟨late, notFree⟩
    have weightsEq : keyWeights setup timeouts leaks bounds horizon scheduler (weights n)
        (some (LateKey.ofView setup timeouts leaks who (execution.logs who)
          (execution.observe (application setup timeouts leaks) who))) =
        weights n (.inr (some ⟨agentLateKey setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler agent, ⟨agent, keyed⟩, rfl⟩)) := by
      have present : some (LateKey.ofView setup timeouts leaks who (execution.logs who)
          (execution.observe (application setup timeouts leaks) who)) ∈ Set.range
            fun agent : {agent : (onePacketN).InformationAgent (onePacketN).playedInformation //
              ownedKeyed (FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon
                scheduler)
                (LateDeliveryAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler)
                  agent} =>
            agentLateKey setup timeouts leaks bounds (initialLaw setup) horizon scheduler agent.1 :=
        ⟨⟨agent, keyed⟩, rfl⟩
      unfold keyWeights
      rw [dite_eq_left_of_eq_true (eq_true present)]
      rfl
    have mixture := freeKeyedMixture_of_keyed (key := agentLateKey setup timeouts leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos scale_le_one
        n)
      (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree keyed
    rw [assembled n]
    change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
    rw [atAgent, mixture, weightsEq]
    exact bind_lateComponent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) _ (scale n) (scale_pos n).le (scale_le_one n) who _
  · intro recorded
    have notLate : ¬ LateDelivery setup timeouts leaks who (some (execution.logs who,
        execution.observe (application setup timeouts leaks) who)) := by
      rintro ⟨_, _, other, same, pending, _⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj same)
      obtain ⟨otherTurn, _, _, unrecorded⟩ := pendingEvent_spec (timeouts := timeouts) pending
      have sameEvent : other = event := Option.some.inj (otherTurn.symm.trans turn)
      subst sameEvent
      rw [recorded] at unrecorded
      cases unrecorded
    have unkeyed : ¬ ownedKeyed (FreeAgent setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler)
        (LateDeliveryAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler)
          agent :=
      fun keyed => notLate keyed.1
    have mixture := freeKeyedMixture_of_not_keyed (key := agentLateKey setup timeouts leaks bounds
      (initialLaw setup) horizon scheduler) (weights n)
      (onePacketUnforced setup timeouts leaks bounds horizon scheduler scale scale_pos scale_le_one
        n)
      (onePacketPrescribed setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n)
      (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one (slots := slots) n) notFree unkeyed
    refine ⟨_, Or.inl rfl, ?_⟩
    rw [assembled n]
    change (onePacketN).agentBehavior _ _ _ agent.1 agent.2.1 = _
    rw [atAgent, mixture]
    rfl

/-- **The owner's debt is clear at an event.** The event has completed, or it is
ready and the owner owes no failure at the decoded point. -/
def DebtClear (who : Player) (event : (graph setup).EventId) :
    (application setup timeouts leaks).ProtocolState → Prop
  | none => True
  | some control => event ∈ control.execution.application.config.cut.completed ∨
      (control.execution.application.config.cut.Ready event ∧
        ∀ point, decodedPoint setup control.execution.application.config = some point →
          ¬ ProtocolState.OwesFailure who setup.program point)

/-- The event of the owner's turn at an information state, if any. -/
def siteTurnEvent (who : Player) : (application setup timeouts leaks).Info → Option (graph
  setup).EventId
  | none => none
  | some (_, view) => view.application.publicView.ownTurn? who

/-- **States through a debt-free site.** States consistent with a site at which
the owner's debt is clear at the site's turn event. -/
def SiteThrough (who : Player) (info : (application setup timeouts leaks).Info)
    (state : (application setup timeouts leaks).ProtocolState) : Prop :=
  SiteConsistent (timeouts := timeouts) who info state ∧
    ∀ event, siteTurnEvent setup timeouts leaks who info = some event → DebtClear setup timeouts
      leaks who event state

/-- **The activation past a site.** At a state whose owner's recall extends the
site's, the first entry past the site's recall was taken at a view showing the
site's pending event as the owner's turn. -/
def SiteActivated (who : Player) (info : (application setup timeouts leaks).Info)
    (state : (application setup timeouts leaks).ProtocolState) : Prop :=
  ∀ control, state = some control → ∀ entry rest,
    control.execution.logs who = infoRecall (timeouts := timeouts) info ++ entry :: rest →
      ∀ event, pendingEvent setup timeouts leaks who info = some event →
        ActivatedAt setup timeouts leaks who event entry

/-- The site is a late delivery, or play past it recalls the activation of its
pending event. -/
def ActivationTracked (who : Player) (info : (application setup timeouts leaks).Info)
    (state : (application setup timeouts leaks).ProtocolState) : Prop :=
  LateDelivery setup timeouts leaks who info ∨ SiteActivated setup timeouts leaks who info state

omit [Fintype Player] [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The control step appends to the recall of an acting player one entry taken at
its current view, and keeps every other player's recall. -/
theorem controlStep_recall_entry (players : Player → (application setup timeouts leaks).Policy)
    (control : (application setup timeouts leaks).Control) {next : (application setup timeouts
      leaks).ProtocolState}
    (member : next ∈ ((application setup timeouts leaks).controlStep (initialLaw setup) horizon
      scheduler
      players (some control)).support) (who : Player) :
    ∃ control', next = some control' ∧
      (control.actor = some who → ∃ entry : (application setup timeouts leaks).PlayerEntry,
        entry.beforeView = control.execution.observe (application setup timeouts leaks) who ∧
          control'.execution.logs who = control.execution.logs who ++ [entry]) ∧
      (control.actor ≠ some who →
        control'.execution.logs who = control.execution.logs who) := by
  rcases control with ⟨remaining, actor, execution⟩
  unfold ReactiveApplication.controlStep at member
  cases actor with
  | none =>
      have idle : (none : Option Player) ≠ some who := fun same => by cases same
      cases remaining with
      | zero =>
          exact ⟨_, (PMF.mem_support_pure_iff _ _).mp member, fun acting => (idle acting).elim,
            fun _ => rfl⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
          obtain ⟨next', supported, rfl⟩ := PMF.support_map .. ▸ moved
          exact ⟨_, rfl, fun acting => (idle acting).elim, fun _ => congrFun
            ((application setup timeouts leaks).environmentStep_recall execution next' command
              supported)
            who⟩
  | some actor =>
      simp only [ReactiveApplication.actor, Option.bind_some] at member
      rw [PMF.mem_support_bind_iff] at member
      obtain ⟨action, _, reached⟩ := member
      refine ⟨_, (PMF.mem_support_pure_iff _ _).mp reached, ?_, ?_⟩
      · intro acting
        cases Option.some.inj acting
        simp only [↓reduceIte, Option.getD_some, ReactiveApplication.Execution.respond]
        rcases action with ⟨_ | _⟩ <;> exact ⟨_, rfl, rfl⟩
      · intro idle
        have different : who ≠ actor := fun same => idle (by rw [same])
        simp only [↓reduceIte, Option.getD_some]
        exact (application setup timeouts leaks).respond_recall_other execution actor who
          different _

omit [Fintype Player] [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The activation stays tracked along play.** A control step from a state
consistent with a site keeps the activation of its pending event tracked: the
first entry past the site's recall is taken at the site's own view. -/
theorem activationTracked_step (players : Player → (application setup timeouts leaks).Policy)
    (who : Player) (info : (application setup timeouts leaks).Info)
    {state : (application setup timeouts leaks).ProtocolState} (consistent : SiteConsistent
      (timeouts := timeouts) who info state)
    (tracked : ActivationTracked setup timeouts leaks who info state)
    {next : (application setup timeouts leaks).ProtocolState}
    (member : next ∈ ((application setup timeouts leaks).controlStep (initialLaw setup) horizon
      scheduler
      players state).support) :
    ActivationTracked setup timeouts leaks who info next := by
  rcases tracked with late | activated
  · exact Or.inl late
  right
  cases state with
  | none => exact consistent.elim
  | some control =>
      obtain ⟨control', rfl, acted, idle⟩ := controlStep_recall_entry setup timeouts leaks horizon
        scheduler players control member who
      intro other otherEq entry rest recallEq event pending
      have same := Option.some.inj otherEq
      subst same
      rcases consistent with ⟨isSome, atSite⟩ | ⟨first, earlier, longer⟩
      · have acting : control.actor = some who := by
          by_contra notActing
          simp only [ReactiveApplication.observe, notActing, ↓reduceIte] at atSite
          rw [← atSite] at isSome
          cases isSome
        obtain ⟨added, before, appended⟩ := acted acting
        simp only [ReactiveApplication.observe, acting, ↓reduceIte] at atSite
        subst atSite
        rw [appended] at recallEq
        change control.execution.logs who ++ [added] =
          control.execution.logs who ++ entry :: rest at recallEq
        obtain ⟨rfl, -⟩ := List.cons.inj (List.append_cancel_left recallEq)
        unfold ActivatedAt
        rw [before]
        exact (pendingEvent_spec (timeouts := timeouts) (setup := setup) pending).1
      · have activatedFirst := activated _ rfl first earlier longer event pending
        by_cases acting : control.actor = some who
        · obtain ⟨added, _, appended⟩ := acted acting
          rw [appended, longer, List.append_assoc, List.cons_append] at recallEq
          obtain ⟨rfl, -⟩ := List.cons.inj (List.append_cancel_left recallEq)
          exact activatedFirst
        · rw [idle acting, longer] at recallEq
          obtain ⟨rfl, -⟩ := List.cons.inj (List.append_cancel_left recallEq)
          exact activatedFirst

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The histories of a site track the activation of its pending event: their
owner's recall is the site's. -/
theorem siteActivated_of_history {who : Player} {site : (onePacketN).InformationSite who}
    (history : (onePacketN).InformationHistory who site.1) :
    SiteActivated setup timeouts leaks who site.1 history.1.state := by
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change (onePacketInformation setup timeouts leaks bounds horizon scheduler).infoOf who trace =
    site.1
    at seen
  rw [onePacket_infoOf] at seen
  intro control current entry rest recallEq event pending
  change state = some control at current
  rw [current] at seen
  by_cases acting : control.actor = some who
  · simp only [ReactiveApplication.observe, acting, ↓reduceIte] at seen
    rw [← seen] at recallEq
    change control.execution.logs who = control.execution.logs who ++ entry :: rest
      at recallEq
    have lengths := congrArg List.length recallEq
    simp at lengths
  · simp only [ReactiveApplication.observe, acting, ↓reduceIte] at seen
    rw [← seen] at pending
    cases pending

omit [Fintype Player] [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Debt stays clear along play.** A control step from an initialized state
keeps the owner's debt clear at an event: its native graph path either completes
the ready event or retains the configuration and its decoded point. -/
theorem debtClear_step (players : Player → (application setup timeouts leaks).Policy)
    (who : Player) (event : (graph setup).EventId) {control : (application setup timeouts
      leaks).Control}
    (clear : DebtClear setup timeouts leaks who event (some control))
    {next : (application setup timeouts leaks).ProtocolState}
    (member : next ∈ ((application setup timeouts leaks).controlStep (initialLaw setup) horizon
      scheduler
      players (some control)).support) :
    DebtClear setup timeouts leaks who event next := by
  obtain ⟨control', rfl, path⟩ := controlStep_graphSteps (timeouts := timeouts) (horizon := horizon)
    (scheduler := scheduler) players control member
  change event ∈ control'.execution.application.config.cut.completed ∨ _
  by_cases completed : event ∈ control'.execution.application.config.cut.completed
  · exact Or.inl completed
  · have ready := (clear.resolve_left fun done =>
      completed (EventGraph.Config.Step.path_completed_mono path done)).1
    have same := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
      (fun other otherReady => setup.eventGraph.sequentialize_ready_unique _ otherReady ready)
      completed path
    rw [same]
    exact clear

open Classical in
omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The site shape of an installed late component, through the site.** Let a
predicate of states refine consistency with a site, and let the activation of
the site key's turn events be recalled at the predicate's states past the site.
Suppose a profile plays, at the site, the late component of an option, and
elsewhere a strategy of the owner that, at the predicate's forced states where
such a turn event is ready and activated, plays the late component of its keyed
weights while the event is unrecorded, and a component whose main part is the
as-if-honest choice or a mixture of late options once it is recorded. Then the
profile has the site shape on the predicate, with the installed option at the
site's key and the keyed weights at every other key. -/
theorem siteComponentShape_of_installed_within
    (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) {slots : Nat} {who : Player}
    (site : (onePacketN).InformationSite who)
    {key : LateKey setup timeouts leaks} (siteKey : lateKey setup timeouts leaks who site.1 = some
      key)
    (option : LateOption slots) (weights : LateKey setup timeouts leaks → PMF (LateOption slots))
    (profile : ∀ player, (onePacketN).BehavioralPolicy player)
    (strategy : (onePacketN).BehavioralPolicy who)
    (allowed : (application setup timeouts leaks).ProtocolState → Prop)
    (within : ∀ state, allowed state → SiteConsistent (timeouts := timeouts) who site.1 state)
    (installed : profile who site.1 =
      slotTrembledChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler scale
        nonnegative le_one who site.1
        ((PMF.pure option).bind (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler assessment who site.1))
        (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler who
          site.1))
        (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment who
          site.1))
    (away : ∀ info, info ≠ site.1 → profile who info = strategy info)
    (activated : ∀ event, (PublicationTurn (timeouts := timeouts) key event ∨ ∃ payload, BindingTurn
      (timeouts := timeouts) key event payload) →
      ∀ (remaining : Nat) (execution : (application setup timeouts leaks).Execution),
        allowed (some ⟨remaining, some who, execution⟩) →
        (∃ entry rest, execution.logs who = infoRecall (timeouts := timeouts) site.1 ++ entry ::
          rest) →
          ∃ entry ∈ execution.logs who, ActivatedAt setup timeouts leaks who event entry)
    (strategyShape : ∀ (history : (onePacketProtocol setup timeouts leaks bounds horizon
        scheduler).History) (remaining : Nat) (execution : (application setup timeouts
          leaks).Execution)
        (event : (graph setup).EventId),
      (PublicationTurn (timeouts := timeouts) key event ∨ ∃ payload, BindingTurn (timeouts :=
        timeouts) key event payload) →
      history.state = some ⟨remaining, some who, execution⟩ →
      allowed history.state →
      ForcedState setup timeouts leaks who history.state →
      execution.application.config.cut.Ready event →
      (∃ entry ∈ execution.logs who, ActivatedAt setup timeouts leaks who event entry) →
      ((eventRecorded timeouts) leaks (execution.logs who) event = false →
        strategy (some (execution.logs who, execution.observe (application setup timeouts leaks)
          who)) =
          slotTrembledChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler scale
            nonnegative le_one who (some (execution.logs who,
              execution.observe (application setup timeouts leaks) who))
            ((weights (LateKey.ofView setup timeouts leaks who (execution.logs who)
                (execution.observe (application setup timeouts leaks) who))).bind
              (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
                assessment who
                (some (execution.logs who, execution.observe (application setup timeouts leaks)
                  who))))
            (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon
              scheduler who
              (some (execution.logs who, execution.observe (application setup timeouts leaks)
                who))))
            (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler assessment
              who
              (some (execution.logs who, execution.observe (application setup timeouts leaks)
                who)))) ∧
      ((eventRecorded timeouts) leaks (execution.logs who) event = true →
        ∃ main : PMF ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
            scheduler).Choice who (some (execution.logs who,
              execution.observe (application setup timeouts leaks) who))),
          (main = honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
              assessment who (some (execution.logs who,
                execution.observe (application setup timeouts leaks) who)) ∨
            ∃ others : PMF (LateOption slots), main = others.bind
              (lateChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
                assessment who
                (some (execution.logs who,
                  execution.observe (application setup timeouts leaks) who)))) ∧
          strategy (some (execution.logs who,
              execution.observe (application setup timeouts leaks) who)) =
            slotTrembledChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
              scale
              nonnegative le_one who (some (execution.logs who,
                execution.observe (application setup timeouts leaks) who)) main
              (PMF.pure (silenceChoice setup timeouts leaks bounds (initialLaw setup) horizon
                scheduler
                who (some (execution.logs who,
                  execution.observe (application setup timeouts leaks) who))))
              (slotChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
                assessment who
                (some (execution.logs who,
                  execution.observe (application setup timeouts leaks) who))))) :
    SiteComponentShape (timeouts := timeouts) assessment scale nonnegative le_one
      (fun other => if other = key then PMF.pure option else weights other) key profile
      allowed := by
  have ownerEq : key.owner = who := owner_of_lateKey (timeouts := timeouts)
    siteKey
  subst ownerEq
  intro event turn history remaining execution current allowedState forced ready
  have consistent := within _ allowedState
  rw [current] at consistent
  by_cases atSite : (application setup timeouts leaks).observe key.owner
      (some ⟨remaining, some key.owner, execution⟩) = site.1
  · have infoEq : site.1 = some (execution.logs key.owner,
        execution.observe (application setup timeouts leaks) key.owner) := by
      rw [← atSite]
      simp only [ReactiveApplication.observe, ↓reduceIte]
    have keyEq : LateKey.ofView setup timeouts leaks key.owner
      (execution.logs key.owner)
        (execution.observe (application setup timeouts leaks) key.owner) = key
          := by
      rw [infoEq] at siteKey
      exact Option.some.inj siteKey
    rw [infoEq] at installed
    constructor
    · intro _
      rw [installed]
      beta_reduce
      rw [keyEq]
      simp only [↓reduceIte]
    · intro _
      exact ⟨_, Or.inr ⟨PMF.pure option, rfl⟩, installed⟩
  · have notSite : some (execution.logs key.owner,
        execution.observe (application setup timeouts leaks) key.owner) ≠
          site.1 := by
      intro same
      apply atSite
      rw [← same]
      simp only [ReactiveApplication.observe, ↓reduceIte]
    have keyNe : LateKey.ofView setup timeouts leaks key.owner
      (execution.logs key.owner)
        (execution.observe (application setup timeouts leaks) key.owner) ≠ key
          := fun same =>
      atSite (siteConsistent_key (timeouts := timeouts) siteKey consistent same)
    have longer : ∃ entry rest, execution.logs key.owner =
        infoRecall (timeouts := timeouts) site.1 ++ entry :: rest := by
      rcases consistent with ⟨_, sameInfo⟩ | longer
      · exact (atSite sameInfo).elim
      · exact longer
    have recalledActivation := activated event turn remaining execution
      (current ▸ allowedState) longer
    have shapes := strategyShape history remaining execution event turn current allowedState
      forced ready recalledActivation
    rw [away _ notSite]
    beta_reduce
    simp only [keyNe, ↓reduceIte]
    exact shapes

omit [Finite setup.intendedProtocol.History] in
/-- **The site shape of the certificate at a pending site.** At a late delivery
or first activation of `who`, the profile installing a late option at the site
and otherwise following a profile assembled from the certificate's components
has the site shape over a predicate of states consistent with the site that
tracks the activation of its pending event, with the installed option at the
site's key and the key weights elsewhere. -/
theorem certificate_siteComponentShape_of_pending
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence) (n : ℕ) {who : Player}
    (site : (onePacketN).InformationSite who)
    (pendingSite : LateDelivery setup timeouts leaks who site.1 ∨ FirstActivation setup timeouts
      leaks who site.1)
    {key : LateKey setup timeouts leaks} (siteKey : lateKey setup timeouts leaks who site.1 = some
      key)
    (option : LateOption slots) (allowed : (application setup timeouts leaks).ProtocolState → Prop)
    (within : ∀ state, allowed state → SiteConsistent (timeouts := timeouts) who site.1 state)
    (tracked : ∀ state, allowed state → ActivationTracked setup timeouts leaks who site.1 state) :
    SiteComponentShape (timeouts := timeouts) (sequence n) (scale n) (scale_pos n).le
      (scale_le_one n)
      (certificateOptions setup timeouts leaks bounds horizon scheduler (weights n) key option) key
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1
          (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
      allowed := by
  obtain ⟨past, view, pendingEvent', atSite, pending⟩ : ∃ past view event,
      site.1 = some (past, view) ∧ pendingEvent setup timeouts leaks who site.1 = some event := by
    rcases pendingSite with ⟨past, view, event, atSite, pending, _⟩ |
      ⟨past, view, event, atSite, pending, _⟩ <;> exact ⟨past, view, event, atSite, pending⟩
  have turn : view.application.publicView.ownTurn? who = some pendingEvent' := by
    have pendingHere := pending
    rw [atSite] at pendingHere
    exact (pendingEvent_spec (timeouts := timeouts) pendingHere).1
  refine siteComponentShape_of_installed_within setup timeouts leaks bounds horizon scheduler
    (sequence n)
    (scale n) (scale_pos n).le (scale_le_one n) site siteKey option
    (fun other => keyWeights setup timeouts leaks bounds horizon scheduler (weights n) (some other))
    _ ((targetSequence n).strategy who) allowed within ?_ ?_ ?_ ?_
  · rw [Profile.update_same, BehavioralPolicy.withLaw_self, PMF.pure_bind]
    rfl
  · intro info different
    rw [Profile.update_same, BehavioralPolicy.withLaw_of_ne _ _ _ different]
  · intro event decided remaining execution allowedState longer
    have keyTurn : key.current.1.ownTurn? key.owner =
      some event := by
      rcases decided with publication | ⟨payload, binding⟩
      · exact publication.1
      · exact binding.1
    have sameEvent : event = pendingEvent' := by
      rw [atSite] at siteKey
      simp only [lateKey, Option.some.injEq] at siteKey
      subst siteKey
      exact Option.some.inj (keyTurn.symm.trans turn)
    subst sameEvent
    obtain ⟨entry, rest, recallEq⟩ := longer
    rcases tracked _ allowedState with late | activated
    · obtain ⟨past', view', event', atSite', pending', earlier, member, activatedAt⟩ := late
      have sameEvent : event' = event := Option.some.inj (pending'.symm.trans pending)
      subst sameEvent
      refine ⟨earlier, ?_, activatedAt⟩
      rw [recallEq]
      exact List.mem_append_left _ (by rw [atSite']; exact member)
    · refine ⟨entry, ?_, activated _ rfl entry rest recallEq event pending⟩
      rw [recallEq]
      exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))
  · intro history remaining execution event _ current _ forcedState ready activated
    exact certificate_strategyShape setup timeouts leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence assembled n who history remaining execution event
      current forcedState ready activated

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The histories of a debt-free pending site pass through it.** At a late
delivery or first activation whose owner owes no failure, every history of the
site's belief is at a state consistent with the site at which the owner's debt
is clear at the site's turn event. -/
theorem siteThrough_of_pendingHistory {who : Player} {site : (onePacketN).InformationSite who}
    (pendingSite : LateDelivery setup timeouts leaks who site.1 ∨ FirstActivation setup timeouts
      leaks who site.1)
    (debtFree : SiteDebtFree setup timeouts leaks bounds horizon scheduler site)
    {key : LateKey setup timeouts leaks} (siteKey : lateKey setup timeouts leaks who site.1 = some
      key)
    (history : (onePacketN).InformationHistory who site.1) :
    SiteThrough setup timeouts leaks who site.1 history.1.state := by
  refine ⟨siteConsistent_of_history (timeouts := timeouts) siteKey history, fun event siteTurn
    => ?_⟩
  obtain ⟨past, view, pending', atSite, pending⟩ : ∃ past view event,
      site.1 = some (past, view) ∧ pendingEvent setup timeouts leaks who site.1 = some event := by
    rcases pendingSite with ⟨past, view, event, atSite, pending, _⟩ |
      ⟨past, view, event, atSite, pending, _⟩ <;> exact ⟨past, view, event, atSite, pending⟩
  rw [atSite] at pending
  obtain ⟨turn, readyView, _, _⟩ := pendingEvent_spec (timeouts := timeouts) (setup := setup)
    pending
  have sameEvent : pending' = event := by
    rw [atSite] at siteTurn
    exact Option.some.inj (turn.symm.trans siteTurn)
  subst sameEvent
  have notOwed := debtFree history
  obtain ⟨⟨state, trace⟩, seen⟩ := history
  change (onePacketInformation setup timeouts leaks bounds horizon scheduler).infoOf who trace =
    site.1
    at seen
  rw [onePacket_infoOf, atSite] at seen
  cases state with
  | none => cases seen
  | some control =>
  rcases control with ⟨remaining, actor, execution⟩
  by_cases active : actor = some who
  swap
  · simp only [ReactiveApplication.observe, active, ↓reduceIte] at seen
    cases seen
  subst active
  simp only [ReactiveApplication.observe, ↓reduceIte] at seen
  obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj seen)
  subst pastEq viewEq
  exact Or.inr ⟨(State.publicView_eventReady _ pending').mp readyView, notOwed⟩


omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **The histories of a debt-free late delivery pass through it**
(`Vegas.siteThrough_of_pendingHistory`). -/
theorem siteThrough_of_history {who : Player} {site : (onePacketN).InformationSite who}
    (late : LateDelivery setup timeouts leaks who site.1)
    (debtFree : SiteDebtFree setup timeouts leaks bounds horizon scheduler site)
    {key : LateKey setup timeouts leaks} (siteKey : lateKey setup timeouts leaks who site.1 = some
      key)
    (history : (onePacketN).InformationHistory who site.1) :
    SiteThrough setup timeouts leaks who site.1 history.1.state :=
  siteThrough_of_pendingHistory setup timeouts leaks bounds horizon scheduler (Or.inl late) debtFree
    siteKey history

/-- **The certificate's lumping at debt-free pending sites.** For an assembled
sequence, at every stage and for every owner, the native kernel of the profiles
installing the late options lumps onto the decision image at late deliveries
and first activations at which the owner owes no failure, with drift twice the
cube of the scale. At a first activation the installed wait option is silence up
to the scale's trembles. Play from such a site stays at states consistent with
it at which the owner's debt is clear at the site's turn event
(`Vegas.debtClear_step`) and the activation of its pending event is recalled
(`Vegas.activationTracked_step`), and the installed profiles have the site shape
there (`Vegas.certificate_siteComponentShape_of_pending`). -/
def certificateLumping (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat} (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence) (n : ℕ) (who : Player) :
    PendingLumpingOn (timeouts := timeouts) (targetSequence n) who
      (fun site => (LateDelivery setup timeouts leaks who site.1 ∨ FirstActivation setup timeouts
        leaks who site.1) ∧
        SiteDebtFree setup timeouts leaks bounds horizon scheduler site)
      (fun site option => Profile.update (sig := (onePacketN).behavioralSignature)
        (targetSequence n).strategy who (((targetSequence n).strategy who).withLaw site.1
          (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale scale_pos
            scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)))
      (DecisionFailed (timeouts := timeouts)) (scale n ^ 3 + scale n ^ 3)
      (DecisionImage (timeouts := timeouts) (setup := setup) (leaks := leaks)) :=
  have nonnegative := (scale_pos n).le
  onePacketLateLumpingOn (timeouts := timeouts) (targetSequence n) who
    (fun site => (LateDelivery setup timeouts leaks who site.1 ∨ FirstActivation setup timeouts
      leaks who site.1) ∧
      SiteDebtFree setup timeouts leaks bounds horizon scheduler site) _
    (by have := pow_nonneg nonnegative 3; linarith) (pow_nonneg nonnegative 3)
    (by linarith) (openingKernel (timeouts := timeouts) bounds horizon scheduler
      (fun key option => lateOpeningSilence (timeouts := timeouts) bounds horizon scheduler
        (sequence n) (scale n)
        nonnegative (scale_le_one n)
        (certificateOptions setup timeouts leaks bounds horizon scheduler (weights n) key option)
          key))
    (fun key option => lateBindingMoves (timeouts := timeouts) bounds horizon scheduler (scale n)
      nonnegative
      (scale_le_one n)
      (certificateOptions setup timeouts leaks bounds horizon scheduler (weights n) key option) key)
    (fun site state => SiteThrough setup timeouts leaks who site.1 state ∧
      ActivationTracked setup timeouts leaks who site.1 state)
    (fun _ relevant _ siteKey history _ _ =>
      ⟨siteThrough_of_pendingHistory setup timeouts leaks bounds horizon scheduler relevant.1
        relevant.2
        siteKey history, Or.inr (siteActivated_of_history setup timeouts leaks bounds horizon
          scheduler
          history)⟩)
    (fun site _ _ state through next member => by
      refine ⟨?_, activationTracked_step setup timeouts leaks horizon scheduler _ who site.1
        through.1.1
        through.2 member⟩
      cases state with
      | none => exact through.1.1.elim
      | some control =>
          exact ⟨siteConsistent_step (timeouts := timeouts) _ who site.1 through.1.1 member, fun
            event siteTurn =>
            debtClear_step setup timeouts leaks horizon scheduler _ who event
              (through.1.2 event siteTurn) member⟩)
    (fun site relevant key siteKey option => ownerStepClose_of_openingLaw (timeouts := timeouts)
      bounds _ key option _
      (ownerOpeningLaw_of_siteComponents (timeouts := timeouts) (sequence n) covers (scale n)
        nonnegative
        (scale_le_one n) (certificateOptions setup timeouts leaks bounds horizon scheduler (weights
          n))
        key option _ _ (certificate_siteComponentShape_of_pending setup timeouts leaks bounds
          horizon
          scheduler sequence scale scale_pos scale_le_one weights targetSequence assembled n site
          relevant.1 siteKey option _ (fun _ through => through.1.1) fun _ through => through.2)))
    (fun site relevant key siteKey option => ownerBindingLaw_of_siteComponents (timeouts :=
      timeouts) (sequence n)
      covers capacity slotsLe (scale n) nonnegative (scale_le_one n)
      (certificateOptions setup timeouts leaks bounds horizon scheduler (weights n)) key option _ _
      (certificate_siteComponentShape_of_pending setup timeouts leaks bounds horizon scheduler
        sequence
        scale scale_pos scale_le_one weights targetSequence assembled n site relevant.1 siteKey
        option _ (fun _ through => through.1.1) fun _ through => through.2))

end Vegas
