/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockProvenance

/-! # Address provenance of gated player submissions -/

noncomputable section

namespace Vegas.ApplicationInstruction

open EventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A submission recognized by an emitted instruction necessarily carries
that instruction's address. This is the local fact preventing an honest gated
owner from placing a future-address packet in the pool. -/
theorem submission_address_of_not_rejects (image : ApplicationImage P L)
    (instruction : ApplicationInstruction P L) (who : P)
    (payload : ApplicationImage.Payload P L)
    (hrecognized : ¬instruction.RejectsCommand image who (.submit payload)) :
    payload.address? = some instruction.address := by
  cases instruction with
  | sample code => exact False.elim (hrecognized trivial)
  | bind code =>
      cases payload <;>
        simp [ApplicationInstruction.RejectsCommand, ApplicationImage.Payload.address?,
          BindingCode.encoding, ChoiceEncoding.submission] at hrecognized ⊢
      all_goals simpa only [ApplicationInstruction.address] using hrecognized.2.1
  | publicChoice code =>
      cases payload <;>
        simp [ApplicationInstruction.RejectsCommand, ApplicationImage.Payload.address?,
          ApplicationImage.choiceEncoding, ChoiceEncoding.submission] at hrecognized ⊢
      all_goals simpa only [ApplicationInstruction.address] using hrecognized.2.1
  | conditional code =>
      have hwho : who = code.endpoint.owner := by
        by_contra hne
        exact hrecognized (by simp [ApplicationInstruction.RejectsCommand, hne])
      subst who
      simp only [ApplicationInstruction.RejectsCommand] at hrecognized
      push Not at hrecognized
      obtain ⟨_, disposition, hdecoded⟩ := hrecognized
      cases hdecode : (code.commandEncoding image disposition).decode (.submit payload) with
      | none => exact False.elim (hdecoded hdecode)
      | some value =>
          have hencode :=
            (code.commandEncoding image disposition).decode_sound (.submit payload) value hdecode
          have haddress := congrArg (fun command => match command with
            | .submit submitted => submitted.address?
            | _ => none) hencode
          cases disposition <;> cases hvalue : code.encoding value
          all_goals simpa only [ConditionalCode.commandEncoding, ChoiceEncoding.submission,
              ChoiceEncoding.trans, ChoiceEncoding.reindex, ChoiceEncoding.atEndpoint,
              ConditionalPublication.addressedChoiceEncoding,
              ConditionalPublication.choiceEncoding,
              ConditionalPublication.addressedDefaultChoiceEncoding,
              ConditionalPublication.defaultChoiceEncoding,
              ConditionalPublication.requestPayload, ApplicationImage.conditionalTransport,
              hvalue, ApplicationImage.Payload.address?, ApplicationInstruction.address] using
                haddress

end Vegas.ApplicationInstruction

namespace Vegas.WindowedApplication

open EventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
/-- Every expiry submission selected by the windowed relay targets the current
active instruction. Thus relay padding cannot introduce a future-address
packet. -/
theorem dueExpiry?_address (runtime : WindowedApplication P L)
    (view : ApplicationImage.Memory P L × Option (Activation Nat))
    (current : ApplicationInstruction P L) (payload : ApplicationImage.Payload P L)
    (hactive : runtime.image.activeAddress? view.1 = some current.address)
    (hdue : runtime.dueExpiry? view = some payload) :
    payload.address? = some current.address := by
  obtain ⟨activation, instruction, _, hactivation, _, hlookup, hexpiry⟩ :=
    runtime.dueExpiry?_some view payload hdue
  have hinstruction : instruction.address = activation.key := by
    have hfound := List.find?_some hlookup
    simpa only [beq_iff_eq] using hfound
  have hcurrent : activation.key = current.address := by
    rw [hactive] at hactivation
    exact (Option.some.inj hactivation).symm
  rw [instruction.expiryPayload?_address payload hexpiry, hinstruction, hcurrent]

end Vegas.WindowedApplication
