module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensLedgerClient
public import Vegas.Pending.ExecutionFacts
public import GameTheory.Math.Probability.ConditionalObservation

@[expose] public section

/-! # Evidence and beliefs for the physical Odds–Evens client -/

noncomputable section

namespace Vegas.Examples.OddsEvensLedgerClient

open OddsEvens EventGraphRuntime Interaction GameTheory.Math.Probability

/-- The graph field containing the first player's Boolean commitment. -/
def evenBinding : EventGraph.FieldRef compiled.layout (.binding even .bool) :=
  ⟨.inr (eventId 0), rfl⟩

private theorem acceptedBit_readout (execution : app.Execution) (who : Player) (bit : Bool)
    (read : acceptedBit? (execution.observe app who) = some bit) :
    ∃ handle, execution.application.accepted evenBinding.field = some handle ∧
      ∃ message ∈ execution.network.ledger,
        message.payload.evidence = some (⟨handle, ⟨.bool, bit⟩⟩ : OpeningFact compiled) := by
  unfold acceptedBit? at read
  change (execution.application.accepted evenBinding.field).bind (fun accepted =>
    execution.network.ledger.findSome? fun message =>
      message.payload.evidence.bind fun fact =>
        if fact.handle = accepted then fact.raw.as? .bool else none) = some bit at read
  cases associated : execution.application.accepted evenBinding.field with
  | none => simp [associated] at read
  | some handle =>
      rw [associated, Option.bind_some, List.findSome?_eq_some_iff] at read
      obtain ⟨earlier, message, suffix, ledger, decoded, _⟩ := read
      refine ⟨handle, rfl, message, ?_, ?_⟩
      · rw [ledger]
        exact List.mem_append_right _ (List.mem_cons_self)
      · cases evidence : message.payload.evidence with
        | none => simp [evidence] at decoded
        | some fact =>
            simp only [evidence, Option.bind_some] at decoded
            split at decoded
            · rename_i same
              rcases fact with ⟨found, raw⟩
              change found = handle at same
              subst found
              rcases raw with ⟨type, value⟩
              by_cases typed : type = .bool
              · subst type
                rw [Raw.as?_mk] at decoded
                cases decoded
                rfl
              · simp [Raw.as?, typed] at decoded
            · contradiction

private theorem stored_of_ledger_certificate (control : app.Control)
    (trace : (app.protocol OddsEvensService.initial OddsEvensService.horizon
      OddsEvensService.scheduler).Trace (some control))
    (handle : Handle compiled) (bit : Bool)
    (associated : control.execution.application.accepted evenBinding.field = some handle)
    (message : Message Player (WitnessedPacket compiled))
    (published : message ∈ control.execution.network.ledger)
    (certified :
      message.payload.evidence = some (⟨handle, ⟨.bool, bit⟩⟩ : OpeningFact compiled)) :
    evenBinding.get? control.execution.application.config.store = some (.success bit) := by
  have nativeTrace : (app.protocol
    ((setup.initialDistribution.map setup.eventInputs).map EventGraphRuntime.State.initial)
    OddsEvensService.horizon OddsEvensService.scheduler).Trace (some control) := by
    rw [PMF.map_comp]
    simpa only [OddsEvensService.initial, Vegas.initialDistribution,
      serviceInitialDistribution, Function.comp_def] using trace
  have facts := EventGraphRuntime.legalFacts timeouts OddsEvensService.leaks _ _ _
    control nativeTrace
  have certificate : (⟨handle, ⟨.bool, bit⟩⟩ : OpeningFact compiled).Holds
      control.execution.application :=
    facts.evidence.ledger message published _ (by
      change _ ∈ message.payload.evidence.toList
      simp [certified])
  exact facts.binding.opening_stored evenBinding handle bit associated certificate

/-- A bit returned by the ledger reader is the actual successful commitment
in every initialized service history, including rejected packets. -/
theorem acceptedBit_stored (control : app.Control)
    (trace : (app.protocol OddsEvensService.initial OddsEvensService.horizon
      OddsEvensService.scheduler).Trace (some control))
    (who : Player) (bit : Bool)
    (read : acceptedBit? (control.execution.observe app who) = some bit) :
    evenBinding.get? control.execution.application.config.store = some (.success bit) := by
  obtain ⟨handle, associated, message, published, certified⟩ :=
    acceptedBit_readout control.execution who bit read
  exact stored_of_ledger_certificate control trace handle bit associated message published certified

/-- The ledger reader recognizes every authentic Boolean certificate for the
accepted handle, even when earlier packets carry unrelated certificates. -/
theorem acceptedBit_eq_some_iff (control : app.Control)
    (trace : (app.protocol OddsEvensService.initial OddsEvensService.horizon
      OddsEvensService.scheduler).Trace (some control))
    (who : Player) (bit : Bool) :
    acceptedBit? (control.execution.observe app who) = some bit ↔
      ∃ handle, control.execution.application.accepted evenBinding.field = some handle ∧
        ∃ message ∈ control.execution.network.ledger,
          message.payload.evidence = some (⟨handle, ⟨.bool, bit⟩⟩ : OpeningFact compiled) := by
  constructor
  · exact acceptedBit_readout control.execution who bit
  · rintro ⟨handle, associated, message, published, certified⟩
    cases read : acceptedBit? (control.execution.observe app who) with
    | none =>
        exfalso
        unfold acceptedBit? at read
        change (control.execution.application.accepted evenBinding.field).bind (fun accepted =>
          control.execution.network.ledger.findSome? fun packet =>
            packet.payload.evidence.bind fun fact =>
              if fact.handle = accepted then fact.raw.as? .bool else none) = none at read
        rw [associated, Option.bind_some, List.findSome?_eq_none_iff] at read
        simpa only [certified, Option.bind_some, ↓reduceIte, Raw.as?_mk,
          Option.some_ne_none] using read message published
    | some found =>
        have stored := stored_of_ledger_certificate control trace handle bit associated message
          published certified
        have readStored := acceptedBit_stored control trace who found read
        exact congrArg some (PublicationResult.success.inj (Option.some.inj (readStored.symm.trans
          stored)))

abbrev information := app.information OddsEvensService.initial OddsEvensService.horizon
  OddsEvensService.scheduler

/-- A decision site's observed certificate determines the committed value in
every hidden history in the site. Every belief at that site therefore gives
probability one to the certified commitment. -/
theorem belief_map_evenBinding_of_read (assessment : information.BehavioralAssessment)
    (site : information.InformationSite odd) (past : List app.PlayerEntry)
    (view : app.PlayerView) (observed : site.1 = some (past, view))
    (bit : Bool) (read : acceptedBit? view = some bit) :
    (assessment.belief odd site).map (fun history =>
      history.1.state.bind fun control =>
        evenBinding.get? control.execution.application.config.store) =
      PMF.pure (some (.success bit)) := by
  have determined (history : information.InformationHistory odd site.1) :
      (history.1.state.bind fun control =>
        evenBinding.get? control.execution.application.config.store) =
        some (.success bit) := by
    have localView : app.observe odd history.1.state = some (past, view) :=
      (app.info OddsEvensService.initial OddsEvensService.horizon
        OddsEvensService.scheduler odd history.1.trace).symm.trans (history.2.trans observed)
    generalize stateEq : history.1.state = state at localView ⊢
    cases state with
    | none => cases localView
    | some control =>
        simp only [ReactiveApplication.observe] at localView
        split at localView
        · have actualView : control.execution.observe app odd = view :=
            congrArg Prod.snd (Option.some.inj localView)
          have nativeTrace := stateEq ▸ history.1.trace
          exact acceptedBit_stored control nativeTrace odd bit (by rw [actualView]; exact read)
        · cases localView
  rw [show (fun history : information.InformationHistory odd site.1 =>
    history.1.state.bind fun control =>
      evenBinding.get? control.execution.application.config.store) =
      Function.const _ (some (.success bit)) from funext determined, PMF.map_const]

/-- Odd's own recall and current physical view at an activation. -/
def oddObservation (execution : app.Execution) : List app.PlayerEntry × app.PlayerView :=
  (execution.logs odd, execution.observe app odd)

/-- For equally weighted physical branches committing the two bits, identical
Odd observation laws suffice for a fair posterior at every observed state of
positive mass. The premises concern the branch laws up to the decision. -/
theorem fiberPosterior_evenBinding_of_equal_observations
    (run : Bool → PMF app.Execution)
    (hidden : (run false).map oddObservation = (run true).map oddObservation)
    (stored : ∀ bit execution, execution ∈ (run bit).support →
      evenBinding.get? execution.application.config.store = some (.success bit))
    (observed : List app.PlayerEntry × app.PlayerView)
    (present : observed ∈ (((uniformLaw Bool).bind run).map oddObservation).support) :
    (fiberPosterior ((uniformLaw Bool).bind run) oddObservation observed).map
      (fun execution => evenBinding.get? execution.application.config.store) =
      (uniformLaw Bool).map (fun bit => some (.success bit)) := by
  let committed := fun execution : app.Execution =>
    evenBinding.get? execution.application.config.store
  let joint := fun execution : app.Execution => (oddObservation execution, committed execution)
  let encode := fun bit : Bool => (some (.success bit) : Option (PublicationResult Bool))
  let viewLaw := (run false).map oddObservation
  have branch (bit : Bool) :
      (run bit).map joint = viewLaw.map (fun view => (view, encode bit)) := by
    have equal : (run bit).map oddObservation = viewLaw := by
      cases bit
      · rfl
      · exact hidden.symm
    rw [← equal, PMF.map_comp]
    exact map_congr_on_support (run bit) fun execution supported =>
      Prod.ext rfl (stored bit execution supported)
  have factor : ((uniformLaw Bool).bind run).map joint =
      bindPairLaw viewLaw (fun _ => (uniformLaw Bool).map encode) := by
    rw [PMF.map_bind]
    simp only [branch]
    calc
      (uniformLaw Bool).bind (fun bit => viewLaw.map fun view => (view, encode bit)) =
          (bindPairLaw ((uniformLaw Bool).map encode) (fun _ => viewLaw)).map Prod.swap := by
        simp only [bindPairLaw, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def]
        rfl
      _ = _ := bindPairLaw_const_map_swap _ _
  have conditioned := map_fiberPosterior_readout ((uniformLaw Bool).bind run) joint Prod.fst
    observed present
  have projected := congrArg (PMF.map Prod.snd) conditioned
  rw [PMF.map_comp, factor, fiberPosterior_snd_bindPairLaw_const] at projected
  exact projected

end Vegas.Examples.OddsEvensLedgerClient
