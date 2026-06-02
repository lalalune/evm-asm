/-
  EvmAsm.EL.SelfdestructEffects

  Pure SELFDESTRUCT post-Cancun side-effect bridge (GH #113).
-/

import EvmAsm.EL.CallValueTransfer
import EvmAsm.EL.MessageCallExecution

namespace EvmAsm.EL

namespace SelfdestructEffects

abbrev CallSideEffects := MessageCallExecution.CallSideEffects

/-- Pure result surface for SELFDESTRUCT state and side effects. -/
structure SelfdestructEffect where
  state : WorldState
  sideEffects : CallSideEffects

/-- Post-Cancun SELFDESTRUCT transfers the account balance to the beneficiary
    and touches the beneficiary, but it does not schedule account deletion.
    Distinctive token: SelfdestructEffects.postCancunSelfdestructEffect. -/
def postCancunSelfdestructEffect
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) : SelfdestructEffect :=
  { state :=
      CallValueTransfer.transferValue
        state account beneficiary accountBalance beneficiaryBalance accountBalance
    sideEffects :=
      { refundCounter := 0
        logs := LogState.empty
        accountsToDelete := []
        touchedAccounts := [beneficiary] } }

theorem postCancunSelfdestructEffect_state
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).state =
      CallValueTransfer.transferValue
        state account beneficiary accountBalance beneficiaryBalance accountBalance := rfl

theorem postCancunSelfdestructEffect_refundCounter
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.refundCounter =
      0 := rfl

theorem postCancunSelfdestructEffect_logs
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.logs =
      LogState.empty := rfl

theorem postCancunSelfdestructEffect_accountsToDelete
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.accountsToDelete =
      [] := rfl

theorem postCancunSelfdestructEffect_touchedAccounts
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance).sideEffects.touchedAccounts =
      [beneficiary] := rfl

theorem postCancunSelfdestructEffect_accountBalance?
    {state : WorldState} {account beneficiary : Address} {accountRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_account : WorldState.getAccount state account = some accountRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (postCancunSelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance).state
        account =
      some (accountBalance - accountBalance) := by
  rw [postCancunSelfdestructEffect_state]
  exact CallValueTransfer.transferValue_callerBalance?
    accountBalance beneficiaryBalance accountBalance h_account h_ne

theorem postCancunSelfdestructEffect_beneficiaryBalance?
    {state : WorldState} {account beneficiary : Address} {beneficiaryRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_beneficiary : WorldState.getAccount state beneficiary = some beneficiaryRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (postCancunSelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance).state
        beneficiary =
      some (beneficiaryBalance + accountBalance) := by
  rw [postCancunSelfdestructEffect_state]
  exact CallValueTransfer.transferValue_calleeBalance?
    accountBalance beneficiaryBalance accountBalance h_beneficiary h_ne

/-- EIP-6780 SELFDESTRUCT effect. Accounts created in the same transaction are
    still deleted; pre-existing accounts keep the post-Cancun transfer-only
    behavior exposed by `postCancunSelfdestructEffect`. -/
def eip6780SelfdestructEffect
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) (createdInSameTx : Bool) :
    SelfdestructEffect :=
  if createdInSameTx then
    let transferredState :=
      CallValueTransfer.transferValue
        state account beneficiary accountBalance beneficiaryBalance accountBalance
    { state := WorldState.deleteAccount transferredState account
      sideEffects :=
        { refundCounter := 0
          logs := LogState.empty
          accountsToDelete := [account]
          touchedAccounts := [beneficiary] } }
  else
    postCancunSelfdestructEffect state account beneficiary accountBalance beneficiaryBalance

theorem eip6780SelfdestructEffect_preExisting_eq_postCancunSelfdestructEffect
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false =
      postCancunSelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance := rfl

theorem eip6780SelfdestructEffect_sameTx_state
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).state =
      WorldState.deleteAccount
        (CallValueTransfer.transferValue
          state account beneficiary accountBalance beneficiaryBalance accountBalance)
        account := rfl

theorem eip6780SelfdestructEffect_sameTx_refundCounter
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).sideEffects.refundCounter =
      0 := rfl

theorem eip6780SelfdestructEffect_sameTx_logs
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).sideEffects.logs =
      LogState.empty := rfl

theorem eip6780SelfdestructEffect_sameTx_accountsToDelete
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).sideEffects.accountsToDelete =
      [account] := rfl

theorem eip6780SelfdestructEffect_sameTx_touchedAccounts
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance true).sideEffects.touchedAccounts =
      [beneficiary] := rfl

theorem eip6780SelfdestructEffect_sameTx_accountDeleted
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    WorldState.getAccount
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance true).state
        account =
      none := by
  rw [eip6780SelfdestructEffect_sameTx_state]
  exact WorldState.getAccount_deleteAccount_same _ _

theorem eip6780SelfdestructEffect_preExisting_refundCounter
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false).sideEffects.refundCounter =
      0 := rfl

theorem eip6780SelfdestructEffect_preExisting_logs
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false).sideEffects.logs =
      LogState.empty := rfl

theorem eip6780SelfdestructEffect_preExisting_accountsToDelete
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false).sideEffects.accountsToDelete =
      [] := rfl

theorem eip6780SelfdestructEffect_preExisting_touchedAccounts
    (state : WorldState) (account beneficiary : Address)
    (accountBalance beneficiaryBalance : Word256) :
    (eip6780SelfdestructEffect
        state account beneficiary accountBalance beneficiaryBalance false).sideEffects.touchedAccounts =
      [beneficiary] := rfl

theorem eip6780SelfdestructEffect_preExisting_accountBalance?
    {state : WorldState} {account beneficiary : Address} {accountRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_account : WorldState.getAccount state account = some accountRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance false).state
        account =
      some (accountBalance - accountBalance) :=
  postCancunSelfdestructEffect_accountBalance?
    accountBalance beneficiaryBalance h_account h_ne

theorem eip6780SelfdestructEffect_preExisting_beneficiaryBalance?
    {state : WorldState} {account beneficiary : Address} {beneficiaryRecord : Account}
    (accountBalance beneficiaryBalance : Word256)
    (h_beneficiary : WorldState.getAccount state beneficiary = some beneficiaryRecord)
    (h_ne : account ≠ beneficiary) :
    WorldState.accountBalance?
        (eip6780SelfdestructEffect
          state account beneficiary accountBalance beneficiaryBalance false).state
        beneficiary =
      some (beneficiaryBalance + accountBalance) :=
  postCancunSelfdestructEffect_beneficiaryBalance?
    accountBalance beneficiaryBalance h_beneficiary h_ne

end SelfdestructEffects

end EvmAsm.EL
