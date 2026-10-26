/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.ProgramPaymentsRuntimeService

/-! # Accepted handles obstruct a Config-only native representation

The experiment uses actual bounded raw actions of the two-activation payment
service. It tests the proposed Config projection before any observable-space
search: native accepted handles are additional operational state.
-/

noncomputable section

namespace Vegas.Examples.ProgramPaymentsNativeRepresentation

open ProgramPayments ProgramPaymentsRuntime
open EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Protocol

abbrev nativeGraph := Vegas.graph (setup 2)
abbrev app := application (setup 2) (leaks 2)

private instance : NeZero nativeGraph.order.eventCount := ⟨by decide⟩

def initial : app.State :=
  EventGraphRuntime.State.initial ((setup 2).eventInputs ProgramPayments.initial)

def start : app.Execution := .initial app initial

def activate (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate .alice⟩] }

theorem activate_law (execution : app.Execution) :
    execution.environmentStep app (.activate .alice) = PMF.pure (activate execution) := by
  have observation : app.observePending = leaks 2 := rfl
  simp only [ReactiveApplication.Execution.environmentStep, observation, leaks,
    PMF.pure_map, MessageNetwork.learn_empty]
  rfl

def includePacket (execution : app.Execution) (identity : MessageId Player) : app.Execution :=
  { execution.includePending app identity with
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .include identity⟩] }

theorem include_law (execution : app.Execution) (identity : MessageId Player) :
    execution.environmentStep app (.include identity) =
      PMF.pure (includePacket execution identity) := by
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

def bindingAction (serial : Fin 2) : app.Action :=
  (runtime (setup 2)).reactiveBinding (leaks 2) .alice 0 .bool (.success true) serial.val

def submitted (serial : Fin 2) : app.Execution :=
  (activate start).respond app .alice (bindingAction serial)

def included (serial : Fin 2) : app.Execution := includePacket (submitted serial) (.alice, 0)

theorem submitted_binding (serial : Fin 2) :
    (submitted serial).application.bindingResult (.alice, .prepared serial.val) .bool =
      .success true := by
  exact reactiveBinding_result (runtime (setup 2)) (leaks 2) .alice 0 .bool
    (.success true) serial.val (activate start) rfl

theorem submitted_config (serial : Fin 2) : (submitted serial).application.config =
    initial.config := rfl

theorem submitted_ready (serial : Fin 2) :
    (submitted serial).application.config.cut.Ready 0 := by
  change initial.config.cut.Ready 0
  decide

def boundConfig : nativeGraph.Config :=
  initial.config.complete 0 (by decide) (.success true) (.success true)

def accepted (serial : Fin 2) : app.State :=
  { (submitted serial).application.complete 0 (submitted_ready serial)
      (.success true) (.success true) with
    accepted := Function.update (submitted serial).application.accepted (.inr 0)
      (some (.alice, .prepared serial.val))
    candidates := (submitted serial).application.candidates.freeze (.alice, .prepared serial.val) }

theorem commitment_handle (serial : Fin 2) :
    handle (runtime (setup 2)) (submitted serial).application
      ⟨(.alice, 0), .commitment 0 (.alice, .prepared serial.val)⟩ = some (accepted serial) := by
  rw [handle_commitment_eq (runtime (setup 2)) (submitted serial).application
    (.alice, 0) 0 (.alice, .prepared serial.val) .alice .bool rfl rfl
    (nodeView_eq_bind rfl rfl) (submitted_ready serial)]
  · rw [submitted_binding]
    rfl
  · change 0 - 0 < 1
    decide
  · rfl
  · rfl
  · rfl
  · intro field
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event =>
        change none ≠ some _
        simp

def bindingCall (serial : Fin 2) : Submission nativeGraph :=
  ⟨.commitment 0 (.alice, .prepared serial.val), some ⟨.bool, true⟩⟩

def envelope (serial : Fin 2) : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(.alice, 0), ⟨.commitment 0 (.alice, .prepared serial.val), none, some ⟨0⟩⟩⟩

theorem initial_token (serial : Fin 2) :
    initial.publicView.tokenFor (.commitment 0 (.alice, .prepared serial.val)) = some ⟨0⟩ := by
  apply PublicView.tokenFor_eq_some _ _ 0 rfl
  intro predecessor member
  exact False.elim (Nat.not_lt_zero _ (nativeGraph.order.predecessor_lt member))

theorem submitted_lookup (serial : Fin 2) :
    (submitted serial).network.lookup (.alice, 0) = some (envelope serial) := by
  change some (⟨(.alice, 0),
    ((runtime (setup 2)).reactiveApplication (leaks 2)).packet
      (((runtime (setup 2)).reactiveApplication (leaks 2)).submit initial .alice
        ⟨bindingCall serial, .none⟩) .alice [] ⟨bindingCall serial, .none⟩⟩ :
      Message Player (WitnessedPacket nativeGraph)) = _
  rw [reactiveApplication_packet_none]
  change some (⟨(.alice, 0), ⟨.commitment 0 (.alice, .prepared serial.val), none,
    initial.publicView.tokenFor (.commitment 0 (.alice, .prepared serial.val))⟩⟩ :
      Message Player (WitnessedPacket nativeGraph)) = _
  rw [initial_token]
  rfl

theorem included_application (serial : Fin 2) :
    (included serial).application = accepted serial := by
  change ((submitted serial).includePending app (.alice, 0)).application = _
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [submitted_lookup]
  change (app.handle (submitted serial).application (envelope serial)).getD _ = _
  rw [reactiveApplication_handle_of_tokenValid (runtime (setup 2)) (leaks 2)
    (submitted serial).application (envelope serial) rfl]
  change (handle (runtime (setup 2)) (submitted serial).application
    ⟨(.alice, 0), .commitment 0 (.alice, .prepared serial.val)⟩).getD _ = _
  rw [commitment_handle]
  rfl

theorem included_config (serial : Fin 2) :
    (included serial).application.config = boundConfig := by
  rw [included_application]
  rfl

theorem included_handle (serial : Fin 2) :
    (included serial).application.accepted (.inr 0) =
      some (.alice, .prepared serial.val) := by
  rw [included_application]
  simp [accepted]

abbrev menu := (bounds 2).rawMenu (runtime (setup 2)) (leaks 2)
abbrev protocol := menu.protocol (Vegas.initialLaw (setup 2)) 9 (service 2).scheduler

theorem initial_law : Vegas.initialLaw (setup 2) = PMF.pure initial := by
  unfold Vegas.initialLaw serviceInitialLaw
  rw [show (setup 2).initialLaw = PMF.pure ProgramPayments.initial from rfl]
  rw [PMF.pure_map]
  rfl

def startTrace : protocol.Trace (some ⟨9, none, start⟩) :=
  .extend .start (fun _ => none) (by
    change ¬ False ∧ ∀ who, ¬ ((none : Option Player) = some who)
    simp) (by
      change some ⟨9, none, start⟩ ∈
        ((Vegas.initialLaw (setup 2)).map
          (fun state => some (⟨9, none, .initial app state⟩ : app.Control))).support
      rw [initial_law, PMF.pure_map]
      simp [start])

private def environmentTrace (remaining : Nat) (execution next : app.Execution)
    (command : app.Command) (trace : protocol.Trace (some ⟨remaining + 1, none, execution⟩))
    (scheduled : (service 2).scheduler execution.environmentRecall
      (execution.observeEnvironment app) = PMF.pure command)
    (realized : execution.environmentStep app command = PMF.pure next) :
    protocol.Trace (some ⟨remaining, command.actor? app, next⟩) :=
  .extend trace (fun _ => none) (by
    change ¬ (remaining + 1 = 0 ∧ (none : Option Player) = none) ∧
      ∀ who, ¬ ((none : Option Player) = some who)
    simp) (by
      change some ⟨remaining, command.actor? app, next⟩ ∈
        (app.transition (Vegas.initialLaw (setup 2)) 9 (service 2).scheduler
          (some ⟨remaining + 1, none, execution⟩) (fun _ => none)).support
      simp only [ReactiveApplication.transition, scheduled, PMF.pure_bind, realized,
        PMF.pure_map]
      simp)

def activatedTrace : protocol.Trace (some ⟨8, some .alice, activate start⟩) :=
  environmentTrace 8 start (activate start) (.activate .alice) startTrace rfl
    (activate_law start)

theorem binding_legal (serial : Fin 2) (past : List app.PlayerEntry) (view : app.PlayerView) :
    bindingAction serial ∈ menu.actions .alice past view := by
  change bindingAction serial ∈ ((bounds 2).rawMenu (runtime (setup 2)) (leaks 2)).actions _ _ _
  unfold MessageBounds.rawMenu
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change ⟨bindingCall serial, .none⟩ ∈ (bounds 2).submissions _
  rw [MessageBounds.submissions_mem]
  refine ⟨⟨serial.isLt, ?_⟩, trivial⟩
  change (⟨.bool, true⟩ : Raw simpleExpr) ∈ rawValues
  exact Finset.mem_image.mpr ⟨true, Finset.mem_univ _, rfl⟩

def submittedTrace (serial : Fin 2) : protocol.Trace (some ⟨8, none, submitted serial⟩) :=
  .extend activatedTrace (fun _ => some (bindingAction serial)) (by
    refine ⟨by change ¬ (8 = 0 ∧ some Player.alice = none); simp, ?_⟩
    intro who
    cases who
    exact ⟨rfl, binding_legal serial _ _⟩) (by
      change some ⟨8, none, submitted serial⟩ ∈
        (app.transition (Vegas.initialLaw (setup 2)) 9 (service 2).scheduler
          (some ⟨8, some .alice, activate start⟩) (fun _ => some (bindingAction serial))).support
      simp [ReactiveApplication.transition, submitted])

theorem include_scheduled (serial : Fin 2) :
    (service 2).scheduler (submitted serial).environmentRecall
      ((submitted serial).observeEnvironment app) = PMF.pure (.include (.alice, 0)) := rfl

def includedTrace (serial : Fin 2) : protocol.Trace (some ⟨7, none, included serial⟩) :=
  environmentTrace 7 (submitted serial) (included serial) (.include (.alice, 0))
    (submittedTrace serial) (include_scheduled serial) (include_law _ _)

def tick (execution : app.Execution) : app.Execution :=
  { execution with
    application := { execution.application with clock := execution.application.clock + 1 }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application .advanceClock⟩] }

theorem tick_law (execution : app.Execution) :
    execution.environmentStep app (.application .advanceClock) = PMF.pure (tick execution) := by
  have law : app.environment execution.application .advanceClock =
      PMF.pure { execution.application with clock := execution.application.clock + 1 } := rfl
  simp only [ReactiveApplication.Execution.environmentStep, law, PMF.pure_map]
  rfl

def expireCompleted (execution : app.Execution) : app.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.expire 0)⟩] }

theorem expireCompleted_law (serial : Fin 2) :
    (tick (included serial)).environmentStep app (.application (.expire 0)) =
      PMF.pure (expireCompleted (tick (included serial))) := by
  have notReady : ¬ (tick (included serial)).application.config.cut.Ready 0 := by
    change ¬ (included serial).application.config.cut.Ready 0
    rw [included_config]
    change ¬ EventOrder.Cut.Ready boundConfig.cut 0
    intro ready
    exact ready.1 (by change 0 ∈ ({0} : Finset (Fin 2)); simp)
  unfold ReactiveApplication.Execution.environmentStep
  change ((environmentStep (runtime (setup 2)) (tick (included serial)).application
    (.expire 0)).map _).map _ = _
  rw [environmentStep_expire_of_not_ready _ _ _ notReady, PMF.pure_map, PMF.pure_map]
  rfl

def secondActivation (serial : Fin 2) : app.Execution :=
  activate (expireCompleted (tick (included serial)))

def secondActivationTrace (serial : Fin 2) :
    protocol.Trace (some ⟨4, some .alice, secondActivation serial⟩) := by
  have ticking : protocol.Trace (some ⟨6, none, tick (included serial)⟩) :=
    environmentTrace 6 _ _ (.application .advanceClock) (includedTrace serial) rfl (tick_law _)
  have expired : protocol.Trace (some ⟨5, none, expireCompleted (tick (included serial))⟩) :=
    environmentTrace 5 _ _ (.application (.expire 0)) ticking rfl (expireCompleted_law serial)
  exact environmentTrace 4 _ _ (.activate .alice) expired rfl (activate_law _)

theorem secondActivation_config (serial : Fin 2) :
    (secondActivation serial).application.config = boundConfig := included_config serial

theorem secondActivation_handle (serial : Fin 2) :
    (secondActivation serial).application.accepted (.inr 0) =
      some (.alice, .prepared serial.val) := included_handle serial

theorem secondActivation_views_differ :
    (secondActivation 0).observe app .alice ≠ (secondActivation 1).observe app .alice := by
  intro same
  have handles := congrArg (fun view : app.PlayerView =>
    view.application.publicView.accepted (.inr 0)) same
  change (secondActivation 0).application.accepted (.inr 0) =
    (secondActivation 1).application.accepted (.inr 0) at handles
  rw [secondActivation_handle, secondActivation_handle] at handles
  cases handles

/-- Failure of this particular quotient on two genuine second-callback histories. -/
theorem no_config_observation_factor :
    ¬ ∃ decode : nativeGraph.Config → app.PlayerView,
      ∀ serial : Fin 2, decode (secondActivation serial).application.config =
        (secondActivation serial).observe app .alice := by
  rintro ⟨decode, correct⟩
  apply secondActivation_views_differ
  rw [← correct 0, ← correct 1, secondActivation_config, secondActivation_config]

theorem second_ready (serial : Fin 2) :
    (secondActivation serial).application.config.cut.Ready 1 := by
  rw [secondActivation_config]
  decide

theorem second_timely (serial : Fin 2) :
    (secondActivation serial).application.WithinDeadline (runtime (setup 2)) 1 := by
  have ready : boundConfig.cut.Ready 1 := by decide
  have unready : ¬ initial.config.cut.Ready 1 := by decide
  have initialNotActivated : initial.activatedAt 1 = none := by
    change EventGraphRuntime.State.refreshActivated initial.config 0 (fun _ => none) 1 = none
    simp only [EventGraphRuntime.State.refreshActivated, dite_eq_right unready]
  have entered : (accepted serial).activatedAt 1 = some 0 := by
    change EventGraphRuntime.State.refreshActivated boundConfig 0
      initial.activatedAt 1 = some 0
    simp only [EventGraphRuntime.State.refreshActivated, dite_eq_left ready]
    change (initial.activatedAt 1).orElse (fun _ => some 0) = _
    rw [initialNotActivated]
    rfl
  change (match (included serial).application.activatedAt 1 with
    | none => False
    | some entered => (included serial).application.clock + 1 - entered < 2)
  rw [included_application]
  rw [entered]
  change 0 + 1 - 0 < 2
  decide

def openingMessage : Message Player (Payload nativeGraph) :=
  ⟨(.alice, 1), .opening 1 (.alice, .prepared 0) ⟨.bool, true⟩⟩

def revealBinding : EventGraph.FieldRef nativeGraph.layout (.binding Player.alice .bool) :=
  ⟨.inr 0, rfl⟩

def revealChecks : List (EventGraph.GuardCheck nativeGraph.layout .bool) :=
  match (nativeGraph.nodes 1 : EventGraph.EventCode nativeGraph.layout (.publication .bool)) with
  | .resolve _ _ _ checks => checks

theorem reveal_code : cast (congrArg (EventGraph.EventCode nativeGraph.layout)
    (show nativeGraph.outputLayout 1 = .publication BaseTy.bool from rfl))
      (nativeGraph.nodes 1) =
        EventGraph.EventCode.resolve (L := simpleExpr) Player.alice BaseTy.bool
          revealBinding revealChecks := rfl

theorem opening_wrong_handle :
    handle (runtime (setup 2)) (secondActivation 1).application openingMessage = none := by
  have notAssociated : (secondActivation 1).application.accepted (.inr 0) ≠
      some (.alice, .prepared 0) := by
    rw [secondActivation_handle]
    decide
  simp only [handle, openingMessage, dite_eq_left (second_ready 1),
    dite_eq_left (second_timely 1),
    nodeView_eq_resolve (graph := nativeGraph) (event := 1) rfl reveal_code]
  simp only [revealBinding, notAssociated, ↓reduceDIte]

theorem second_candidate :
    (secondActivation 0).application.candidates.lookup (.alice, .prepared 0) =
      .openable ⟨.bool, true⟩ := by
  change (included 0).application.candidates.lookup _ = _
  rw [included_application]
  change (((initial.candidates.prepare .alice (.prepared 0) ⟨.bool, true⟩).freeze
    (.alice, .prepared 0)).freeze (.alice, .prepared 0)).lookup (.alice, .prepared 0) = _
  simp only [CommitmentCandidates.lookup_freeze_self, CommitmentCandidates.lookup_prepare_self]
  rfl

def opened : app.State :=
  (secondActivation 0).application.complete 1 (second_ready 0) true (.success true)

theorem opening_correct_handle :
    handle (runtime (setup 2)) (secondActivation 0).application openingMessage = some opened := by
  exact handle_opening_eq (runtime (setup 2)) (secondActivation 0).application (.alice, 1) 1
    (.alice, .prepared 0) .alice .bool revealBinding revealChecks rfl reveal_code
    (nodeView_eq_resolve rfl reveal_code) (second_ready 0) (second_timely 0) rfl rfl
    (secondActivation_handle 0) true second_candidate (by
      rw [secondActivation_config]
      rfl) (.success true) (by
        rw [secondActivation_config]
        rfl)

/-- The same admitted raw opening has different operational effects at equal Configs. -/
theorem no_config_handle_factor :
    ¬ ∃ execute : nativeGraph.Config → Option nativeGraph.Config,
      ∀ serial : Fin 2,
        (handle (runtime (setup 2)) (secondActivation serial).application openingMessage).map
          EventGraphRuntime.State.config =
            execute (secondActivation serial).application.config := by
  rintro ⟨execute, correct⟩
  have first := correct 0
  have second := correct 1
  rw [secondActivation_config] at first second
  have equal := first.trans second.symm
  rw [opening_correct_handle, opening_wrong_handle] at equal
  cases equal

def openingCall : Submission nativeGraph :=
  ⟨openingMessage.payload, none⟩

def openingAction : app.Action := ⟨some ⟨openingCall, .none⟩⟩

def openingSubmitted (serial : Fin 2) : app.Execution :=
  (secondActivation serial).respond app .alice openingAction

def openingEnvelope : Message Player (WitnessedPacket nativeGraph) :=
  ⟨(.alice, 1), ⟨openingMessage.payload, none, some ⟨1⟩⟩⟩

theorem second_token (serial : Fin 2) :
    (secondActivation serial).application.publicView.tokenFor openingMessage.payload =
      some ⟨1⟩ := by
  apply PublicView.tokenFor_eq_some _ _ 1 rfl
  intro predecessor member
  have earlier := nativeGraph.order.predecessor_lt member
  have same : predecessor = 0 := Fin.ext (by
    change predecessor.val < 1 at earlier
    change predecessor.val = 0
    omega)
  subst predecessor
  change 0 ∈ (secondActivation serial).application.config.history.map EventGraph.Completion.event
  rw [secondActivation_config]
  change 0 ∈ [0]
  simp

theorem openingSubmitted_lookup (serial : Fin 2) :
    (openingSubmitted serial).network.lookup (.alice, 1) = some openingEnvelope := by
  change some (⟨(.alice, 1), app.packet
    (app.submit (secondActivation serial).application .alice ⟨openingCall, .none⟩)
      .alice ((secondActivation serial).network.known .alice) ⟨openingCall, .none⟩⟩ :
        Message Player (WitnessedPacket nativeGraph)) = _
  rw [reactiveApplication_packet_none]
  change some (⟨(.alice, 1), ⟨openingMessage.payload, none,
    (secondActivation serial).application.publicView.tokenFor openingMessage.payload⟩⟩ :
      Message Player (WitnessedPacket nativeGraph)) = _
  rw [second_token]
  rfl

def completed : app.Execution := includePacket (openingSubmitted 0) (.alice, 1)

theorem completed_application : completed.application = opened := by
  change ((openingSubmitted 0).includePending app (.alice, 1)).application = _
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [openingSubmitted_lookup]
  change (app.handle (secondActivation 0).application openingEnvelope).getD _ = _
  rw [reactiveApplication_handle_of_tokenValid (runtime (setup 2)) (leaks 2)
    (secondActivation 0).application openingEnvelope rfl]
  change (handle (runtime (setup 2)) (secondActivation 0).application openingMessage).getD _ = _
  rw [opening_correct_handle]
  rfl

theorem opening_legal (past : List app.PlayerEntry) (view : app.PlayerView) :
    openingAction ∈ menu.actions .alice past view := by
  change openingAction ∈ ((bounds 2).rawMenu (runtime (setup 2)) (leaks 2)).actions _ _ _
  unfold MessageBounds.rawMenu
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change ⟨openingCall, .none⟩ ∈ (bounds 2).submissions _
  rw [MessageBounds.submissions_mem]
  refine ⟨⟨⟨by change 0 < 2; decide, ?_⟩, trivial⟩, trivial⟩
  change (⟨.bool, true⟩ : Raw simpleExpr) ∈ rawValues
  exact Finset.mem_image.mpr ⟨true, Finset.mem_univ _, rfl⟩

def openingSubmittedTrace (serial : Fin 2) :
    protocol.Trace (some ⟨4, none, openingSubmitted serial⟩) :=
  .extend (secondActivationTrace serial) (fun _ => some openingAction) (by
    refine ⟨by change ¬ (4 = 0 ∧ some Player.alice = none); simp, ?_⟩
    intro who
    cases who
    exact ⟨rfl, opening_legal _ _⟩) (by
      change some ⟨4, none, openingSubmitted serial⟩ ∈
        (app.transition (Vegas.initialLaw (setup 2)) 9 (service 2).scheduler
          (some ⟨4, some .alice, secondActivation serial⟩) (fun _ => some openingAction)).support
      simp [ReactiveApplication.transition, openingSubmitted])

theorem opening_include_scheduled :
    (service 2).scheduler (openingSubmitted 0).environmentRecall
      ((openingSubmitted 0).observeEnvironment app) = PMF.pure (.include (.alice, 1)) := rfl

def completedTrace : protocol.Trace (some ⟨3, none, completed⟩) :=
  environmentTrace 3 (openingSubmitted 0) completed (.include (.alice, 1))
    (openingSubmittedTrace 0) opening_include_scheduled (include_law _ _)

theorem completed_config_terminal : completed.application.config.cut.Terminal := by
  rw [completed_application]
  change (EventOrder.Cut.complete (secondActivation 0).application.config.cut 1
    (second_ready 0)).Terminal
  change insert 1 (secondActivation 0).application.config.cut.completed = Finset.univ
  rw [secondActivation_config]
  change ({1, 0} : Finset (Fin 2)) = Finset.univ
  decide

end Vegas.Examples.ProgramPaymentsNativeRepresentation
