module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveCanonicalDecision
public import Vegas.Pending.EffectiveOpening
public import Vegas.Pending.EffectiveAction
public import Vegas.Expr.Simple

@[expose] public section

/-! # Public traffic from a guard-rejected opening

Both initial bits yield a failed publication and the same graph observation at
the other player's first decision. The actual client sends the opening in both
worlds, so the included packet lets that player recover the bit even with
pending observation disabled.
-/

noncomputable section

namespace VegasTests.GuardRejectedTraffic

open Vegas Vegas.EventGraph Vegas.EventGraphRuntime Interaction

abbrev order : EventOrder where
  eventCount := 2
  predecessors event := if event = 0 then ∅ else {0}
  predecessor_lt := by decide

abbrev inputs : Fin 1 → EventField Bool simpleExpr := fun _ => .binding false .bool
abbrev outputs : Fin 2 → EventField Bool simpleExpr :=
  Fin.cases (.publication .bool) (fun _ => .binding true .bool)
abbrev layout := fieldLayout inputs outputs

abbrev binding : FieldRef layout (.binding false .bool) := ⟨.inl 0, rfl⟩

def rejects : GuardCheck layout .bool where
  subject := 0
  payload := .bool
  code := { schema := [], schemaNames := by decide, subjectFresh := by decide,
            code := .constBool false }
  subjectRead := .proposed
  reads := fun ref _ => nomatch ref
  readFields := ∅
  subject_mem := by intro field impossible; cases impossible
  reads_mem := fun ref => nomatch ref

abbrev release : EventCode layout (.publication .bool) :=
  EventCode.resolve (layout := layout) false BaseTy.bool binding [rejects]

abbrev graph : Vegas.EventGraph Bool simpleExpr where
  inputCount := 1
  order := order
  inputLayout := inputs
  outputLayout := outputs
  nodes := Fin.cases (motive := fun event => EventCode layout (outputs event))
    release (fun _ => EventCode.bind (layout := layout) true BaseTy.bool)
  reads_available := by
    intro event field member
    fin_cases event
    · have eq : field = Sum.inl (0 : Fin 1) := by
        simpa [EventCode.readFields, GuardCheck.listReadFields, rejects] using member
      subst field
      trivial
    · exact (Finset.notMem_empty _ member).elim
  payoffs := []

abbrev publication : graph.EventId := 0
abbrev answer : graph.EventId := 1

abbrev values (bit : Bool) : graph.Inputs := fun _ => .success bit
abbrev timeouts : EventTimeouts graph := ⟨fun _ => 5⟩
abbrev app := (reactiveApplication timeouts) (fun _ _ => PMF.pure ∅)
abbrev start (bit : Bool) : app.Execution := ReactiveApplication.Execution.initial app
  (Vegas.EventGraphRuntime.State.initial (graph := graph) (values bit))

abbrev choice : graph.Action publication := true


theorem opening_rejected (bit : Bool) :
    openingAccepted publication (start bit).application.config.store = false := by
  rw [openingAccepted, nodeView_eq_resolve (outputEq := rfl) (codeEq := rfl)]
  rfl

def rawOfCall (call : Payload graph) : Option Bool :=
  match call with
  | .opening _ _ raw => raw.as? .bool
  | _ => none

abbrev sent (bit : Bool) : app.Execution :=
  (start bit).respond app false
    (canonicalServiceDecision timeouts _ false [] ((start bit).observe app false)
      publication choice)

abbrev delivered (bit : Bool) : app.Execution :=
  (sent bit).includePending app (false, 0)

theorem observed_bit (bit : Bool) :
    ((delivered bit).observe app true).messages.ledger.map ((fun packet => rawOfCall packet.call) ∘
      Message.payload) = [some bit] := by
  rfl

theorem ready (bit : Bool) : (start bit).application.config.cut.Ready publication := by
  cases bit <;> decide

abbrev advanced (bit : Bool) : Vegas.EventGraphRuntime.State graph :=
  (start bit).application.complete publication (ready bit) choice .failure

theorem resolves_to_failure (bit : Bool) :
    (start bit).application.config.step publication (ready bit) choice =
      PMF.pure (advanced bit).config := by
  change (PMF.pure (PublicationResult.failure : PublicationResult Bool)).map _ = _
  rw [PMF.pure_map]
  rfl

theorem graph_observation_equal :
    graph.playerObserve true (advanced false).config =
      graph.playerObserve true (advanced true).config := by
  apply EventPlayerObservation.ext
  · rfl
  · funext field
    rcases field with input | event
    · fin_cases input
      rfl
    · fin_cases event <;> rfl
  · rfl
  · rfl

abbrev acceptedHandle : Handle graph := (false, .initial (0 : Fin 1))

theorem delivered_application (bit : Bool) : (delivered bit).application = advanced bit := by
  have timely : (start bit).application.WithinDeadline timeouts publication := by
    change 0 < 5
    decide
  have active : false ∉ (start bit).application.config.defaulted := by
    cases bit <;> decide
  have handled := handle_opening_eq timeouts (start bit).application (false, 0) publication
    acceptedHandle false BaseTy.bool binding [rejects] rfl rfl (nodeView_eq_resolve rfl rfl)
    (ready bit) timely active rfl rfl rfl bit rfl rfl .failure rfl
  have clear : ∀ event, ¬ (advanced bit).AutomaticReady event := by
    cases bit <;> decide
  change ((handle timeouts (start bit).application
    ⟨(false, 0), .opening publication acceptedHandle ⟨BaseTy.bool, bit⟩⟩).map
      Vegas.EventGraphRuntime.State.drain).getD (start bit).application = _
  rw [handled, Option.map_some, Option.getD_some]
  exact Vegas.EventGraphRuntime.State.drain_eq_of_clear _ clear

theorem answer_ready (bit : Bool) : (delivered bit).application.config.cut.Ready answer := by
  rw [delivered_application]
  cases bit <;> decide

theorem no_graph_response_recovers_bit :
    ¬ ∃ response : graph.PlayerObservation true → PMF Bool,
      ∀ bit, response (graph.playerObserve true (advanced bit).config) = PMF.pure bit := by
  rintro ⟨response, agrees⟩
  have same := (agrees false).symm.trans ((congrArg response graph_observation_equal).trans
    (agrees true))
  have drawn : false ∈ (PMF.pure false).support := (PMF.mem_support_pure_iff _ _).mpr rfl
  rw [same, PMF.mem_support_pure_iff] at drawn
  cases drawn

theorem realizable (bits : PMF Bool) (reference : graph.BehavioralProfile) :
    RealizableProfile (bits.map values) reference := by
  intro initial supported config reached event _ready action _chosen
  obtain ⟨bit, _, rfl⟩ := PMF.support_map .. ▸ supported
  have inputEq : config.inputs = values bit := by
    clear _chosen _ready action event
    induction reached with
    | initial => rfl
    | step _ event ready action next member ih =>
        exact (EventGraph.Config.Step.inputs_eq ⟨event, ready, action, member⟩).trans ih
  fin_cases event
  · change EffectiveAction config publication action
    rw [EffectiveAction, nodeView_eq_resolve (outputEq := rfl) (codeEq := rfl)]
    intro _
    refine ⟨bit, ?_⟩
    change config.store (.inl (0 : Fin 1)) = _
    rw [EventGraph.Config.store_input, inputEq]
  · change EffectiveAction config answer action
    rw [EffectiveAction, nodeView_eq_bind (outputEq := rfl) (codeEq := rfl)]
    trivial

end VegasTests.GuardRejectedTraffic
