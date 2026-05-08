/-
  EvmAsm.Evm64.SDiv.HandlerBridge

  Connects the pure SDIV opcode handler to the SDIV stack-execution bridge.
-/

import EvmAsm.Evm64.ArithmeticHandlers
import EvmAsm.Evm64.SDiv.StackExecutionBridge

namespace EvmAsm.Evm64
namespace SDivStackExecutionBridge

theorem sdivHandler_stack_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackResult}
    (h_run : runSDivStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.sdivHandler state).stack =
      out.effects.stackWords ++ out.stack := by
  rw [runSDivStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  subst h_out
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
    SDivArgs.sdivResultFromArgs_eq, SDivArgs.sdivArgs, h_stack]

theorem sdivHandler_status_of_runSDivStack?_some
    {state : EvmState} {out : SDivStackResult}
    (h_run : runSDivStack? { stack := state.stack } = some out) :
    (ArithmeticHandlers.sdivHandler state).status = state.status := by
  rw [runSDivStack?_eq_some_iff] at h_run
  rcases h_run with ⟨dividend, divisor, rest, h_stack, h_out⟩
  simp at h_stack
  simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
    EvmState.withStack, h_stack]

theorem sdivHandler_status_of_runSDivStack?_none
    {state : EvmState}
    (h_run : runSDivStack? { stack := state.stack } = none) :
    (ArithmeticHandlers.sdivHandler state).status = .error := by
  cases h_stack : state.stack with
  | nil =>
      simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
        h_stack]
  | cons dividend tail =>
      cases h_tail : tail with
      | nil =>
          simp [ArithmeticHandlers.sdivHandler, ArithmeticHandlers.binaryHandler,
            h_stack, h_tail]
      | cons divisor rest =>
          simp [runSDivStack?, SDivArgsStackDecode.decodeSDivStack?,
            stackRestAfterSDiv?, Option.bind, h_stack, h_tail] at h_run

end SDivStackExecutionBridge
end EvmAsm.Evm64
