module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensClientOutput
public import Vegas.Pending.ReactiveCanonicalMenu
public import Vegas.Pending.ReactiveBoundedHandles
public import Vegas.Examples.OddsEvensClientRecall

@[expose] public section

/-! # Bounded responses of the Odds–Evens ledger client -/

noncomputable section

namespace Vegas.Examples.OddsEvensExecutableClient

open OddsEvens OddsEvensLedgerClient EventGraphRuntime EventGraph Interaction
open GameTheory.Math.Probability

local notation "limits" => OddsEvensService.timeouts
local notation "leaks" => OddsEvensService.leaks
local notation "alphabet" => OddsEvens.bounds
local notation "menu" => OddsEvens.bounds.rawMenu OddsEvensService.timeouts OddsEvensService.leaks

def ownBinding (who : Player) : Fin 4 := if who then 1 else 0

private theorem binding_event_owner (who : Player) (event : Fin 4)
    (binding : event = 0 ∨ event = 1) (owned : compiled.actor? event = some who) :
    event = ownBinding who := by
  rcases binding with rfl | rfl <;> cases who <;> first | rfl | cases owned

private theorem bindingCount_at_ownBinding (who : Player) (view : app.PlayerView)
    (selected : view.application.publicView.ownTurn? who = some (ownBinding who)) :
    view.application.publicView.bindingCount who = 0 := by
  have absent := (view.application.publicView.ownTurn?_spec who (ownBinding who) selected).1.1
  rw [← countCompletedBindings_eq]
  unfold countCompletedBindings
  apply List.countP_eq_zero.mpr
  intro event member
  change Fin 4 at event
  fin_cases event <;> cases who <;> first | decide | exact (absent member).elim

private theorem firstFresh_from_recall (execution : app.Execution) (who : Player)
    (known : CandidateRecall limits leaks execution)
    (slots : submittedCandidateSlots limits leaks (execution.logs who) = [])
    (selected : (execution.observe app who).application.publicView.ownTurn? who =
      some (ownBinding who)) :
    canonicalFreshSlot who (execution.observe app who).application = some 0 := by
  let view := execution.observe app who
  have count := bindingCount_at_ownBinding who view selected
  have fresh : view.application.candidates (.prepared (view.application.publicView.bindingCount
      who)) = .fresh := by
    rw [count]
    exact known who 0 (by simp [slots])
  rw [canonicalFreshSlot_canonical who view.application fresh, count]

private theorem silent_mem (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView) :
    (⟨none⟩ : app.Action) ∈ (menu).actions who past view := by
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  trivial

private theorem binding_mem (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (active : who ∉ view.application.publicView.observation.defaulted)
    (selected : canonicalFreshSlot who view.application = some 0) (bit : Bool) :
    (if who then ordinaryResponse who past view (eventId 1) (some (.success bit))
      else ordinaryResponse who past view (eventId 0) (some (.success bit))) ∈
      (menu).actions who past view := by
  have packet_mem (event : Fin 4) :
      reactiveBinding limits leaks who event BaseTy.bool (.success bit) 0 ∈
        (menu).actions who past view := by
    rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    change _ ∈ (alphabet).submissions _
    rw [MessageBounds.submissions_mem]
    refine ⟨⟨?_, Finset.mem_image.mpr ⟨bit, Finset.mem_univ _, rfl⟩⟩, trivial⟩
    change 0 < OddsEvens.bounds.candidateCount
    decide
  cases who
  · simp only [Bool.false_eq_true, ↓reduceIte, ordinaryResponse]
    exact (canonicalServiceDecision_binding limits leaks false past view (eventId 0)
      BaseTy.bool rfl rfl rfl active 0 selected (.success bit)) ▸ packet_mem 0
  · simp only [↓reduceIte, ordinaryResponse]
    exact (canonicalServiceDecision_binding limits leaks true past view (eventId 1)
      BaseTy.bool rfl rfl rfl active 0 selected (.success bit)) ▸ packet_mem 1

private theorem opening_mem (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (event : Fin 4) (owner : Player)
    (binding : FieldRef compiled.layout (.binding owner .bool))
    (checks : List (GuardCheck compiled.layout BaseTy.bool))
    (outputEq : compiled.outputLayout event = .publication .bool)
    (codeEq : cast (congrArg (EventCode compiled.layout) outputEq) (compiled.nodes event) =
      EventCode.resolve (L := simpleExpr) (layout := compiled.layout)
        owner BaseTy.bool binding checks)
    (handles : ∀ field candidate, view.application.publicView.accepted field = some candidate →
      (alphabet).AllowsHandle candidate) :
    ordinaryResponse who past view event
      (cast (congrArg EventField.Action outputEq.symm) true) ∈ (menu).actions who past view := by
  classical
  let choice : compiled.Action event := cast (congrArg EventField.Action outputEq.symm) true
  change canonicalServiceDecision limits leaks who past view event choice ∈ _
  apply (alphabet).menu_in_raw limits leaks who past view
  apply (alphabet).canonicalServiceDecision_available limits leaks
  have node := nodeView_eq_resolve outputEq codeEq
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · simp only [canonicalReactiveDecision, inactive, ↓reduceIte]
    exact silent_mem who past view
  · simp only [canonicalReactiveDecision, ite_eq_right inactive, node]
    cases sent : reactiveResolutionPacket who event BaseTy.bool binding checks outputEq choice
        view.application with
    | none =>
        simp only [Option.map_none]
        exact silent_mem who past view
    | some packet =>
        simp only [Option.map_some]
        rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
        change _ ∈ (alphabet).submissions _
        have allowed := (alphabet).resolutionPacket_allowed who event BaseTy.bool binding checks
          outputEq choice view.application
          (fun bit => Finset.mem_image.mpr ⟨bit, Finset.mem_univ _, rfl⟩) handles packet sent
        have before := (alphabet).disclosureSubmission_allowed packet [] allowed
        have after := ((alphabet).submissions_mem _ _).mp
          ((alphabet).normalize_submission_mem who view.application [] _
            (((alphabet).submissions_mem _ _).mpr before))
        exact ((alphabet).submissions_mem _ _).mpr
          ⟨after.1, (alphabet).allowsEvidence_mono (List.nil_subset _) _ after.2⟩

private theorem ledgerRaw_mem (who : Player) (past : List app.PlayerEntry)
    (view : app.PlayerView)
    (action : app.Action)
    (allowed : action ∈ (menu).actions who
      (past.map (ReactiveApplication.PlayerEntry.ledgerOnly app)) (view.ledgerOnly app)) :
    action ∈ (menu).actions who past view := by
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at allowed ⊢
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => trivial
  | some submission =>
      change submission ∈ (alphabet).submissions
        (ReactiveApplication.ResponseMenu.knownPackets
          (past.map (ReactiveApplication.PlayerEntry.ledgerOnly app)) (view.ledgerOnly app))
        at allowed
      change submission ∈ (alphabet).submissions
        (ReactiveApplication.ResponseMenu.knownPackets past view)
      rw [MessageBounds.submissions_mem] at allowed ⊢
      refine ⟨allowed.1, (alphabet).allowsEvidence_mono ?_ _ allowed.2⟩
      unfold ReactiveApplication.ResponseMenu.knownPackets ReactiveApplication.outputs
      simp only [ReactiveApplication.PlayerEntry.ledgerOnly,
        ReactiveApplication.PlayerView.ledgerOnly, List.filterMap_map, Function.comp_def,
        List.append_nil]
      intro message inLedger
      rcases List.mem_append.mp inLedger with prior | ledger
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl prior)))
      · exact List.mem_append.mpr (Or.inr ledger)

/-- On a legal history consistent with the acting player's own prior client
responses, every packet of the prescribed response law fits the raw menu.
The opponent's earlier legal responses are unrestricted. -/
theorem client_policy_mem_of_compatible (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : ((menu).protocol OddsEvensService.initial horizon scheduler).Trace (some control))
    (who : Player) (compatible : (policy who).Consistent (control.execution.logs who))
    (action : app.Action) (chosen : action ∈
      (policy who (control.execution.logs who) (control.execution.observe app who)).support) :
    action ∈ (menu).actions who (control.execution.logs who)
      (control.execution.observe app who) := by
  let prior := control.execution.logs who
  let current := control.execution.observe app who
  let past := prior.map (ReactiveApplication.PlayerEntry.ledgerOnly app)
  let view := current.ledgerOnly app
  let inputs : PMF compiled.Inputs := setup.initialDistribution.map setup.eventInputs
  have initialEq : inputs.map (State.initial (graph := compiled)) = OddsEvensService.initial := by
    simp only [inputs, OddsEvensService.initial, Vegas.initialDistribution,
      serviceInitialDistribution, PMF.map_comp, Function.comp_def]
  have handles : ∀ field candidate, view.application.publicView.accepted field = some candidate →
      (alphabet).AllowsHandle candidate := by
    have trace' : ((menu).protocol (inputs.map (State.initial (graph := compiled)))
      horizon scheduler).Trace (some control) := initialEq.symm ▸ trace
    exact ((alphabet).executionHandles_raw_history limits leaks inputs horizon scheduler trace').1
  have known : CandidateRecall limits leaks control.execution := by
    have trace' : (app.protocol (inputs.map (State.initial (graph := compiled)))
      horizon scheduler).Trace (some control) :=
      initialEq.symm ▸ (menu).toRawTrace OddsEvensService.initial horizon scheduler trace
    exact candidateRecall_history limits leaks inputs horizon scheduler trace'
  rw [← decideResponse_distribution] at chosen
  change action ∈ (((uniformLaw Bool).map (fun coin =>
    encodeResponse who past view (decideResponse (decodeObservation who past view) coin)))).support
    at chosen
  obtain ⟨coin, _, rfl⟩ := PMF.support_map .. ▸ chosen
  apply ledgerRaw_mem
  by_cases inactive : who ∈ view.application.publicView.observation.defaulted
  · simp only [decodeObservation, inactive, ↓reduceIte, decideResponse, encodeResponse]
    exact silent_mem who past view
  cases turn : view.application.publicView.ownTurn? who with
  | none =>
      simp only [decodeObservation, ite_eq_right inactive, turn, decideResponse, encodeResponse]
      exact silent_mem who past view
  | some event =>
      cases sent : eventRecorded limits leaks past event with
      | true =>
          simp only [decodeObservation, ite_eq_right inactive, turn, sent, ↓reduceIte,
            decideResponse, encodeResponse]
          exact silent_mem who past view
      | false =>
          simp only [decodeObservation, ite_eq_right inactive, turn, sent, Bool.false_eq_true,
            ↓reduceIte]
          have permitBinding (binding : event = eventId 0 ∨ event = eventId 1) (bit : Bool) :
              (if who then ordinaryResponse who past view (eventId 1) (some (.success bit))
                else ordinaryResponse who past view (eventId 0) (some (.success bit))) ∈
                (menu).actions who past view := by
            have same := binding_event_owner who event binding
              (view.application.publicView.ownTurn?_spec who event turn).2
            have unsent : eventRecorded limits leaks prior (eventId (ownBinding who)) = false := by
              change event = eventId (ownBinding who) at same
              rw [← same]
              simpa only [past, eventRecorded, List.any_map, Function.comp_def,
                ReactiveApplication.PlayerEntry.ledgerOnly] using sent
            have slots := submittedCandidateSlots_eq_nil_of_compatible who prior compatible unsent
            have fresh := firstFresh_from_recall control.execution who known slots (same ▸ turn)
            exact binding_mem who past view inactive fresh bit
          change Fin 4 at event
          fin_cases event
          · have owner : who = false :=
              (Option.some.inj
                (view.application.publicView.ownTurn?_spec who (eventId 0) turn).2).symm
            subst who
            exact permitBinding (Or.inl rfl) coin
          · have owner : who = true :=
              (Option.some.inj
                (view.application.publicView.ownTurn?_spec who (eventId 1) turn).2).symm
            subst who
            exact permitBinding (Or.inr rfl) ((acceptedBit? view).elim coin (!·))
          · let binding : FieldRef compiled.layout (.binding even .bool) :=
              ⟨.inr (0 : Fin 4), rfl⟩
            exact opening_mem who past view (eventId 2) even binding _ rfl rfl handles
          · let binding : FieldRef compiled.layout (.binding odd .bool) :=
              ⟨.inr (1 : Fin 4), rfl⟩
            exact opening_mem who past view (eventId 3) odd binding _ rfl rfl handles

/-- Silence after an unsupported own response gives a total admissible policy
while leaving prescribed play intact on consistent recall. -/
theorem recoverWithSilence_admissible (horizon : Nat) (scheduler : app.Scheduler)
    (who : Player) :
    (menu).Admissible OddsEvensService.initial horizon scheduler who
      ((policy who).recover app.silentPolicy) := by
  intro control trace _ action chosen
  by_cases compatible : (policy who).Consistent (control.execution.logs who)
  · rw [ReactiveApplication.Policy.recover_eq _ _ _ _ compatible] at chosen
    exact client_policy_mem_of_compatible horizon scheduler control trace who compatible
      action chosen
  · rw [ReactiveApplication.Policy.recover_eq_recovery _ _ _ _ compatible] at chosen
    obtain rfl := app.silentPolicy_cases _ _ action chosen
    exact silent_mem who _ _

end Vegas.Examples.OddsEvensExecutableClient
