/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceCalendar
import VegasTests.SelectiveAssociationNamedEvidence

/-! # Deterministic source prefixes retaining arbitrary earlier responses

The functions here evaluate the declared calendar. They retain the full
network, receipts, private observations, and own-action recall. In particular,
neither ambient response is replaced by silence in the prefix statements.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory.Math.Probability

def recordEnvironment {Claim : Type} (before after : (application Claim).Execution)
    (cmd : (application Claim).Command) : (application Claim).Execution :=
  { after with environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment (application Claim), cmd⟩] }

def effect {Claim : Type} (execution : (application Claim).Execution)
    (cmd : (application Claim).Command) : (application Claim).Execution :=
  let after := match cmd with
    | .activate who =>
        { execution with
          network := execution.network.learn who (if who = bob then {(alice, 0)} else ∅) }
    | .include id => execution.includePending (application Claim) id
    | .application cmd => { execution with application := command execution.application cmd }
    | .wait => execution
  recordEnvironment execution after cmd

theorem effect_law {Claim : Type} (execution : (application Claim).Execution)
    (cmd : (application Claim).Command) :
    execution.environmentStep (application Claim) cmd = FinDist.pure (effect execution cmd) := by
  cases cmd <;>
    simp only [ReactiveApplication.Execution.environmentStep, application, leaks,
      FinDist.map_pure] <;> rfl

theorem effect_recall {Claim : Type} (execution : (application Claim).Execution)
    (cmd : (application Claim).Command) (who : Player) :
    (effect execution cmd).recall who = execution.recall who := by
  exact congrFun ((application Claim).environmentStep_recall execution (effect execution cmd) cmd
    (by rw [effect_law]; exact FinDist.mem_support_pure.mpr rfl)) who

theorem effect_environmentRecall {Claim : Type} (execution : (application Claim).Execution)
    (cmd : (application Claim).Command) :
    (effect execution cmd).environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment (application Claim), cmd⟩] := rfl

theorem include_application {Claim : Type} (execution : (application Claim).Execution)
    (id : MessageId Player) :
    (execution.includePending (application Claim) id).application = execution.application := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  cases execution.network.lookup id <;> rfl

theorem effect_application {Claim : Type} (execution : (application Claim).Execution)
    (cmd : (application Claim).Command) :
    (effect execution cmd).application = match cmd with
      | .application command => NamedSource.command execution.application command
      | _ => execution.application := by
  cases cmd with
  | activate | application | wait => rfl
  | «include» id => exact include_application execution id

theorem submit_visit {Claim : Type} (state : State) (who : Player)
    (submission : Submission Claim) : (submit state who submission).visit = state.visit := by
  unfold submit
  split
  · split
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
    · rfl
  · rfl

theorem respond_visit {Claim : Type} (execution : (application Claim).Execution)
    (who : Player) (action : (application Claim).Action) :
    (execution.respond (application Claim) who action).application.visit =
      execution.application.visit := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit submission => exact submit_visit execution.application who submission
      | replay id =>
          cases (execution.network.known who).find? (fun message => message.id = id) <;> rfl

theorem respond_early_core {Claim : Type} (execution : (application Claim).Execution)
    (who : Player) (action : (application Claim).Action)
    (early : execution.application.visit = none) :
    (execution.respond (application Claim) who action).application.core =
      execution.application.core := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit submission => exact early_claim_core execution.application who submission early
      | replay id =>
          cases (execution.network.known who).find? (fun message => message.id = id) <;> rfl

def firstResponse {Claim : Type} (first : (application Claim).Action) :
    (application Claim).Execution :=
  (effect (root Claim) (.activate alice)).respond (application Claim) alice first

def prelude {Claim : Type} (first second : (application Claim).Action) :
    (application Claim).Execution :=
  (effect (firstResponse first) (.activate bob)).respond (application Claim) bob second

def aliceInput {Claim : Type} (first second : (application Claim).Action) :
    (application Claim).Execution :=
  effect (effect (prelude first second) (.application (.grant 0))) (.activate alice)

theorem firstResponse_core {Claim : Type} (first : (application Claim).Action) :
    (firstResponse first).application.core = initialCore :=
  respond_early_core _ alice first rfl

theorem firstResponse_visit {Claim : Type} (first : (application Claim).Action) :
    (firstResponse first).application.visit = none :=
  respond_visit _ alice first

theorem prelude_visit {Claim : Type} (first second : (application Claim).Action) :
    (prelude first second).application.visit = none := by
  rw [prelude, respond_visit, effect_application]
  exact firstResponse_visit first

theorem prelude_core {Claim : Type} (first second : (application Claim).Action) :
    (prelude first second).application.core = initialCore := by
  rw [prelude, respond_early_core]
  · rw [effect_application]
    exact firstResponse_core first
  · rw [effect_application]
    exact firstResponse_visit first

theorem aliceInput_core {Claim : Type} (first second : (application Claim).Action) :
    (aliceInput first second).application.core = initialCore := by
  rw [aliceInput, effect_application, effect_application]
  exact prelude_core first second

theorem aliceInput_visit {Claim : Type} (first second : (application Claim).Action) :
    (aliceInput first second).application.visit = some 0 := rfl

def remainingVisit {Claim : Type} (event : Event) (execution : (application Claim).Execution) :
    (application Claim).Execution :=
  let recorded := effect execution (latest (execution.observeEnvironment (application Claim)) event)
  let timed := (List.replicate (2 ^ event.val) ()).foldl
    (fun current _ => effect current (.application .tick)) recorded
  effect timed (.application (.settle event))

def carolInput {Claim : Type} (first second binding : (application Claim).Action) :
    (application Claim).Execution :=
  let sent := (aliceInput first second).respond (application Claim) alice binding
  effect (effect (remainingVisit 0 sent) (.application (.grant 1))) (.activate carol)

def bobInput {Claim : Type} (first second binding guess : (application Claim).Action) :
    (application Claim).Execution :=
  let sent := (carolInput first second binding).respond (application Claim) carol guess
  effect (effect (remainingVisit 1 sent) (.application (.grant 2))) (.activate bob)

def selectedBinding {Claim : Type} (event : Event) (action : (application Claim).Action) :
    PublicationResult Bool :=
  match action.transmission with
  | some (.submit submission) =>
      if submission.address = some event ∧ submission.kind = .bind then submission.binding
      else .failure
  | _ => .failure

theorem latest_application {Claim : Type} (execution : (application Claim).Execution)
    (event : Event) :
    (effect execution
      (latest (execution.observeEnvironment (application Claim)) event)).application =
      execution.application := by
  unfold latest
  split <;> simp only [effect_application]

theorem ticks_core {Claim : Type} (execution : (application Claim).Execution) (count : Nat) :
    ((List.replicate count ()).foldl
      (fun current _ => effect current (.application .tick)) execution).application.core =
        execution.application.core := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.foldl_cons, ih, effect_application]
      rfl

theorem remainingVisit_core {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) :
    (remainingVisit event execution).application.core =
      if (coreStage execution.application.core).val = event.val then
        coreAdvance execution.application.core .failure false else execution.application.core := by
  unfold remainingVisit
  rw [effect_application]
  simp only [command]
  split <;> simp_all only [ticks_core, latest_application, ↓reduceIte]

theorem respond_application {Claim : Type} (execution : (application Claim).Execution)
    (who : Player) (action : (application Claim).Action) :
    (execution.respond (application Claim) who action).application =
      match action.transmission with
      | some (.submit submission) => submit execution.application who submission
      | _ => execution.application := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit => rfl
      | replay id =>
          cases (execution.network.known who).find? (fun message => message.id = id) <;> rfl

theorem carolInput_core {Claim : Type} (first second binding : (application Claim).Action) :
    (carolInput first second binding).application.core =
      CorePath.alice (selectedBinding 0 binding) := by
  rw [carolInput, effect_application, effect_application]
  change (remainingVisit 0 _).application.core = _
  rw [remainingVisit_core, respond_application]
  have initial_stage : coreStage initialCore = 0 := rfl
  have alice_stage (a : PublicationResult Bool) : coreStage (CorePath.alice a) = 1 := rfl
  rcases binding with ⟨transmission⟩
  cases transmission with
  | none =>
      simpa only [selectedBinding, aliceInput_core, initial_stage, Fin.val_zero, ↓reduceIte] using
        CorePath.initial_advance .failure false
  | some transmission =>
      cases transmission with
      | replay =>
          simpa only [selectedBinding, aliceInput_core, initial_stage, Fin.val_zero,
            ↓reduceIte] using
            CorePath.initial_advance .failure false
      | submit submission =>
          simp only [submit, aliceInput_visit, selectedBinding]
          cases address : submission.address with
          | none =>
              simpa only [aliceInput_core, initial_stage, Fin.val_zero, reduceCtorEq, false_and,
                ↓reduceIte] using CorePath.initial_advance .failure false
          | some event =>
              by_cases same : event = 0
              · subst event
                by_cases kind : submission.kind = .bind
                · simp [kind, aliceInput_core, initial_stage, eventOwner, bindingOwner,
                    CorePath.initial_advance, alice_stage]
                · simp [kind, aliceInput_core, initial_stage, eventOwner, bindingOwner,
                    CorePath.initial_advance]
              · simp [same, aliceInput_core, initial_stage, eventOwner, bindingOwner,
                  CorePath.initial_advance]

theorem carolInput_visit {Claim : Type} (first second binding : (application Claim).Action) :
    (carolInput first second binding).application.visit = some 1 := rfl

theorem bobInput_visit {Claim : Type} (first second binding guess : (application Claim).Action) :
    (bobInput first second binding guess).application.visit = some 2 := rfl

theorem bobInput_core {Claim : Type} (first second binding guess : (application Claim).Action) :
    (bobInput first second binding guess).application.core =
      CorePath.carol (selectedBinding 0 binding) (selectedBinding 1 guess) := by
  rw [bobInput, effect_application, effect_application]
  change (remainingVisit 1 _).application.core = _
  rw [remainingVisit_core, respond_application]
  have alice_stage (a : PublicationResult Bool) : coreStage (CorePath.alice a) = 1 := rfl
  have carol_stage (a c : PublicationResult Bool) : coreStage (CorePath.carol a c) = 2 := rfl
  rcases guess with ⟨transmission⟩
  cases transmission with
  | none =>
      simpa only [selectedBinding, carolInput_core, alice_stage, Fin.val_one, ↓reduceIte] using
        CorePath.alice_advance (selectedBinding 0 binding) .failure false
  | some transmission =>
      cases transmission with
      | replay =>
          simpa only [selectedBinding, carolInput_core, alice_stage, Fin.val_one,
            ↓reduceIte] using
            CorePath.alice_advance (selectedBinding 0 binding) .failure false
      | submit submission =>
          simp only [submit, carolInput_visit, selectedBinding]
          cases address : submission.address with
          | none =>
              simpa only [selectedBinding, carolInput_core, alice_stage, Fin.val_one,
                reduceCtorEq, false_and,
                ↓reduceIte] using
                CorePath.alice_advance (selectedBinding 0 binding) .failure false
          | some event =>
              by_cases same : event = 1
              · subst event
                by_cases kind : submission.kind = .bind
                · simp [kind, carolInput_core, alice_stage, eventOwner, bindingOwner,
                    CorePath.alice_advance, carol_stage]
                  rfl
                · simp [kind, carolInput_core, alice_stage, eventOwner, bindingOwner,
                    CorePath.alice_advance]
                  rfl
              · simp [same, carolInput_core, alice_stage, eventOwner, bindingOwner,
                  CorePath.alice_advance]
                rfl

theorem effect_sound {Claim : Type} (execution : (application Claim).Execution)
    (cmd : (application Claim).Command) (sound : (packetEvidence Claim).Sound execution) :
    (packetEvidence Claim).Sound (effect execution cmd) :=
  (packetEvidence Claim).sound_environment execution (effect execution cmd) cmd sound
    (by rw [effect_law]; exact FinDist.mem_support_pure.mpr rfl)

theorem aliceInput_sound {Claim : Type} (first second : (application Claim).Action) :
    (packetEvidence Claim).Sound (aliceInput first second) := by
  apply effect_sound
  apply effect_sound
  apply (packetEvidence Claim).sound_respond
  apply effect_sound
  apply (packetEvidence Claim).sound_respond
  apply effect_sound
  exact (packetEvidence Claim).sound_initial initial

theorem aliceInput_known_empty {Claim : Type} (first second : (application Claim).Action)
    (who : Player) (message : Message Player (Packet Claim))
    (known : message ∈ (aliceInput first second).network.known who) :
    message.payload.evidence = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro fact certified
  have valid := (aliceInput_sound first second).known who message known fact
    (Finset.mem_toList.mpr certified)
  change ((aliceInput first second).application.core).evidenceHolds
    sourceProgram fact.toSource at valid
  rw [aliceInput_core] at valid
  exact initial_no_evidence fact.toSource valid

theorem submit_clock {Claim : Type} (state : State) (who : Player)
    (submission : Submission Claim) : (submit state who submission).clock = state.clock := by
  unfold submit
  split
  · split
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
    · rfl
  · rfl

theorem respond_clock {Claim : Type} (execution : (application Claim).Execution)
    (who : Player) (action : (application Claim).Action) :
    (execution.respond (application Claim) who action).application.clock =
      execution.application.clock := by
  rw [respond_application]
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit submission => exact submit_clock execution.application who submission
      | replay => rfl

theorem ticks_clock {Claim : Type} (execution : (application Claim).Execution) (count : Nat) :
    ((List.replicate count ()).foldl
      (fun current _ => effect current (.application .tick)) execution).application.clock =
        execution.application.clock + count := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.foldl_cons, ih, effect_application]
      change execution.application.clock + 1 + count = execution.application.clock + (count + 1)
      omega

theorem remainingVisit_clock {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) :
    (remainingVisit event execution).application.clock =
      execution.application.clock + 2 ^ event.val := by
  unfold remainingVisit
  rw [effect_application]
  simp only [command]
  split <;> simp only [ticks_clock, latest_application]

theorem aliceInput_clock {Claim : Type} (first second : (application Claim).Action) :
    (aliceInput first second).application.clock = 0 := by
  simp only [aliceInput, effect_application, command, prelude, respond_clock,
    firstResponse]
  rfl

theorem carolInput_clock {Claim : Type} (first second binding : (application Claim).Action) :
    (carolInput first second binding).application.clock = 1 := by
  rw [carolInput, effect_application, effect_application]
  change (remainingVisit 0 _).application.clock = _
  rw [remainingVisit_clock, respond_clock, aliceInput_clock]
  rfl

theorem bobInput_clock {Claim : Type} (first second binding guess : (application Claim).Action) :
    (bobInput first second binding guess).application.clock = 3 := by
  rw [bobInput, effect_application, effect_application]
  change (remainingVisit 1 _).application.clock = _
  rw [remainingVisit_clock, respond_clock, carolInput_clock]
  rfl

theorem aliceInput_application {Claim : Type} (first second : (application Claim).Action) :
    (aliceInput first second).application = ⟨initialCore, some 0, 0⟩ := by
  calc
    _ = (⟨(aliceInput first second).application.core,
        (aliceInput first second).application.visit,
        (aliceInput first second).application.clock⟩ : State) := rfl
    _ = _ := by rw [aliceInput_core, aliceInput_visit, aliceInput_clock]

end VegasTests.SelectiveAssociation.NamedSource
