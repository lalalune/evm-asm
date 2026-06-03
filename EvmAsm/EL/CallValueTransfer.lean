/-
  EvmAsm.EL.CallValueTransfer

  Pure CALL value-transfer world-state effect (GH #114).  This module
  records the balance movement for the value-transferring CALL case.
  Balance sufficiency, account creation rules, and the full handler
  stack/state specs remain later slices.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.MessageCall
import EvmAsm.EL.WorldStateAccount

namespace EvmAsm.EL
namespace CallValueTransfer

/-- Debit `value` from the caller and credit it to the callee.

    This helper assumes the caller/callee account records already exist
    and the caller has sufficient balance.  Those preconditions are
    intentionally left to the later executable handler/spec layer; here
    we expose the pure state transformer and projection lemmas. -/
def transferValue
    (state : WorldState) (caller callee : Address)
    (callerBalance calleeBalance value : Word256) : WorldState :=
  let state' := WorldState.setAccountBalance state caller (callerBalance - value)
  WorldState.setAccountBalance state' callee (calleeBalance + value)

/-- Apply the value-transfer effect carried by a message-call frame, given the
    concrete pre-call balances for caller and callee. -/
def transferFrameValue
    (state : WorldState) (frame : CallFrame)
    (callerBalance calleeBalance : Word256) : WorldState :=
  transferValue state frame.caller frame.callee callerBalance calleeBalance
    frame.transferredValue

theorem transferValue_state
    (state : WorldState) (caller callee : Address)
    (callerBalance calleeBalance value : Word256) :
    transferValue state caller callee callerBalance calleeBalance value =
      WorldState.setAccountBalance
        (WorldState.setAccountBalance state caller (callerBalance - value))
        callee (calleeBalance + value) := rfl

theorem transferFrameValue_eq_transferValue
    (state : WorldState) (frame : CallFrame) (callerBalance calleeBalance : Word256) :
    transferFrameValue state frame callerBalance calleeBalance =
      transferValue state frame.caller frame.callee callerBalance calleeBalance
        frame.transferredValue := rfl

theorem transferValue_callerBalance?
    {state : WorldState} {caller callee : Address}
    {callerAccount : Account}
    (callerBalance calleeBalance value : Word256)
    (h_caller : WorldState.getAccount state caller = some callerAccount)
    (h_ne : caller ≠ callee) :
    WorldState.accountBalance?
        (transferValue state caller callee callerBalance calleeBalance value)
        caller =
      some (callerBalance - value) := by
  rw [transferValue_state]
  have h_after_caller :
      WorldState.getAccount
          (WorldState.setAccountBalance state caller (callerBalance - value))
          caller =
        some { callerAccount with balance := callerBalance - value } :=
    WorldState.getAccount_setAccountBalance_same h_caller
  rw [WorldState.accountBalance?, WorldState.getAccount_setAccountBalance_ne]
  · simp [h_after_caller]
  · exact h_ne

theorem transferValue_calleeBalance?
    {state : WorldState} {caller callee : Address}
    {calleeAccount : Account}
    (callerBalance calleeBalance value : Word256)
    (h_callee : WorldState.getAccount state callee = some calleeAccount)
    (h_ne : caller ≠ callee) :
    WorldState.accountBalance?
        (transferValue state caller callee callerBalance calleeBalance value)
        callee =
      some (calleeBalance + value) := by
  rw [transferValue_state]
  exact WorldState.accountBalance?_setAccountBalance_same
    (state := WorldState.setAccountBalance state caller (callerBalance - value))
    (addr := callee)
    (account := calleeAccount)
    (by
      rw [WorldState.getAccount_setAccountBalance_ne]
      · exact h_callee
      · exact fun h_eq => h_ne h_eq.symm)

theorem transferValue_otherAccount
    (state : WorldState) {caller callee other : Address}
    (callerBalance calleeBalance value : Word256)
    (h_other_caller : other ≠ caller) (h_other_callee : other ≠ callee) :
    WorldState.getAccount
        (transferValue state caller callee callerBalance calleeBalance value)
        other =
      WorldState.getAccount state other := by
  rw [transferValue_state]
  rw [WorldState.getAccount_setAccountBalance_ne (h_ne := h_other_callee)]
  rw [WorldState.getAccount_setAccountBalance_ne (h_ne := h_other_caller)]


/-! ### Transaction-level value transfer -/

/-- Apply the front-door transaction state effects around value movement.

    This touches/creates the recipient account, debits the sender balance,
    bumps the sender nonce, and credits the recipient balance. Gas settlement,
    fee recipient accounting, and balance sufficiency checks are intentionally
    left to later slices. -/
def transferTransactionValue
    (state : WorldState) (sender recipient : Address)
    (senderBalance recipientBalance value : Word256) (senderNonce : Nat) : WorldState :=
  let touchedState := WorldState.ensureAccount state recipient
  let debitedState := WorldState.setAccountBalance touchedState sender (senderBalance - value)
  let nonceState := WorldState.setAccountNonce debitedState sender (senderNonce + 1)
  WorldState.setAccountBalance nonceState recipient (recipientBalance + value)

theorem transferTransactionValue_state
    (state : WorldState) (sender recipient : Address)
    (senderBalance recipientBalance value : Word256) (senderNonce : Nat) :
    transferTransactionValue state sender recipient senderBalance recipientBalance value
        senderNonce =
      WorldState.setAccountBalance
        (WorldState.setAccountNonce
          (WorldState.setAccountBalance
            (WorldState.ensureAccount state recipient)
            sender (senderBalance - value))
          sender (senderNonce + 1))
        recipient (recipientBalance + value) := rfl

theorem transferTransactionValue_senderBalance?
    {state : WorldState} {sender recipient : Address}
    {senderAccount : Account}
    (senderBalance recipientBalance value : Word256) (senderNonce : Nat)
    (h_sender : WorldState.getAccount state sender = some senderAccount)
    (h_ne : sender ≠ recipient) :
    WorldState.accountBalance?
        (transferTransactionValue state sender recipient senderBalance recipientBalance value
          senderNonce)
        sender =
      some (senderBalance - value) := by
  rw [transferTransactionValue_state]
  rw [WorldState.accountBalance?_setAccountBalance_ne (h_ne := h_ne)]
  rw [WorldState.accountBalance?_setAccountNonce]
  exact WorldState.accountBalance?_setAccountBalance_same
    (by
      rw [WorldState.getAccount_ensureAccount_ne]
      · exact h_sender
      · exact h_ne)

theorem transferTransactionValue_senderNonce?
    {state : WorldState} {sender recipient : Address}
    {senderAccount : Account}
    (senderBalance recipientBalance value : Word256) (senderNonce : Nat)
    (h_sender : WorldState.getAccount state sender = some senderAccount)
    (h_ne : sender ≠ recipient) :
    WorldState.accountNonce?
        (transferTransactionValue state sender recipient senderBalance recipientBalance value
          senderNonce)
        sender =
      some (senderNonce + 1) := by
  rw [transferTransactionValue_state]
  rw [WorldState.accountNonce?_setAccountBalance]
  exact WorldState.accountNonce?_setAccountNonce_same
    (by
      exact WorldState.getAccount_setAccountBalance_same
        (balance := senderBalance - value)
        (by
          rw [WorldState.getAccount_ensureAccount_ne]
          · exact h_sender
          · exact h_ne))

theorem transferTransactionValue_existingRecipientBalance?
    {state : WorldState} {sender recipient : Address}
    {recipientAccount : Account}
    (senderBalance recipientBalance value : Word256) (senderNonce : Nat)
    (h_recipient : WorldState.getAccount state recipient = some recipientAccount)
    (h_ne : sender ≠ recipient) :
    WorldState.accountBalance?
        (transferTransactionValue state sender recipient senderBalance recipientBalance value
          senderNonce)
        recipient =
      some (recipientBalance + value) := by
  rw [transferTransactionValue_state]
  exact WorldState.accountBalance?_setAccountBalance_same
    (by
      rw [WorldState.getAccount_setAccountNonce_ne (h_ne := h_ne.symm)]
      rw [WorldState.getAccount_setAccountBalance_ne (h_ne := h_ne.symm)]
      exact WorldState.getAccount_ensureAccount_existing h_recipient)

theorem transferTransactionValue_newRecipientBalance?
    {state : WorldState} {sender recipient : Address}
    (senderBalance value : Word256) (senderNonce : Nat)
    (h_recipient_missing : WorldState.getAccount state recipient = none)
    (h_ne : sender ≠ recipient) :
    WorldState.accountBalance?
        (transferTransactionValue state sender recipient senderBalance 0 value senderNonce)
        recipient =
      some value := by
  rw [transferTransactionValue_state]
  simpa using
    (WorldState.accountBalance?_setAccountBalance_same
      (state := WorldState.setAccountNonce
        (WorldState.setAccountBalance (WorldState.ensureAccount state recipient)
          sender (senderBalance - value))
        sender (senderNonce + 1))
      (addr := recipient)
      (balance := 0 + value)
      (by
        rw [WorldState.getAccount_setAccountNonce_ne (h_ne := h_ne.symm)]
        rw [WorldState.getAccount_setAccountBalance_ne (h_ne := h_ne.symm)]
        exact WorldState.getAccount_ensureAccount_missing h_recipient_missing))

theorem transferFrameValue_forStaticCall
    (state : WorldState) (caller callee : Address) (input : List Byte) (gas : Nat)
    (callerBalance calleeBalance : Word256) :
    transferFrameValue state (CallFrame.forStaticCall caller callee input gas)
        callerBalance calleeBalance =
      transferValue state caller callee callerBalance calleeBalance 0 := rfl

theorem transferFrameValue_forDelegateCall
    (state : WorldState) (caller callee : Address) (apparentValue : Word256)
    (input : List Byte) (gas : Nat) (isStatic : Bool)
    (callerBalance calleeBalance : Word256) :
    transferFrameValue
        state
        (CallFrame.forDelegateCall caller callee apparentValue input gas isStatic)
        callerBalance calleeBalance =
      transferValue state caller callee callerBalance calleeBalance 0 := rfl

theorem transferFrameValue_forCall
    (state : WorldState) (caller callee : Address) (value : Word256)
    (input : List Byte) (gas : Nat) (isStatic : Bool)
    (callerBalance calleeBalance : Word256) :
    transferFrameValue
        state (CallFrame.forCall caller callee value input gas isStatic)
        callerBalance calleeBalance =
      transferValue state caller callee callerBalance calleeBalance value := rfl

end CallValueTransfer
end EvmAsm.EL
