/-
  EvmAsm.Evm64.SMod.HandlerBridge

  Connects the pure SMOD opcode handler to the SMOD stack-execution bridge.
-/

import EvmAsm.Evm64.ArithmeticHandlers
import EvmAsm.Evm64.SMod.StackExecutionBridge

namespace EvmAsm.Evm64
namespace SModStackExecutionBridge

theorem smodHandler_stack_of_runSModStack?_some
    {state : EvmState} {out : SModStackResult}
    (h_run : runSModStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.smodHandler state).stack =
      out.effects.stackWords ++ out.stack := by
  rw [runSModStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  subst h_out
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    SModArgs.smodResultFromArgs_eq, SModArgs.smodArgs, h_stack]

theorem smodHandler_status_of_runSModStack?_some
    {state : EvmState} {out : SModStackResult}
    (h_run : runSModStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.smodHandler state).status = state.status := by
  rw [runSModStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
    EvmState.withStack, h_stack]

theorem smodHandler_status_of_runSModStack?_none
    {state : EvmState}
    (h_run : runSModStack? { stack := state.stack } = none) :
    (ArithmeticHandlers.smodHandler state).status = .error := by
  cases h_stack : state.stack with
  | nil =>
      simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
        h_stack]
  | cons dividend tail =>
      cases h_tail : tail with
      | nil =>
          simp [ArithmeticHandlers.smodHandler, ArithmeticHandlers.binaryHandler,
            h_stack, h_tail]
      | cons divisor rest =>
          simp [runSModStack?, SModArgsStackDecode.decodeSModStack?,
            stackRestAfterSMod?, Option.bind, h_stack, h_tail] at h_run

end SModStackExecutionBridge
end EvmAsm.Evm64
