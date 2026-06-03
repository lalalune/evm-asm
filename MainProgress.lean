/-
  MainProgress

  Entry point for `lake exe progress-report`. Prints the registry-driven
  sections of `PROGRESS.md` to stdout. The shell wrapper at
  `scripts/progress-report.sh` composes this with grep-derived sections
  (per-opcode cycle bounds, codegen milestones, CI invariants).
-/

import EvmAsm.Progress

open EvmAsm.Progress

private def tierLabel : ProofTier → String
  | .proven      => "proven"
  | .partly      => "partial"
  | .conditional => "conditional"
  | .execSpec    => "execSpec"
  | .notStarted  => "notStarted"

private def tierIcon : ProofTier → String
  | .proven      => "✅"
  | .partly      => "🟡"
  | .conditional => "🔶"
  | .execSpec    => "⏳"
  | .notStarted  => "✗"

private def fmtRow (e : OpcodeEntry) : String :=
  let proofCell := e.proofRef.getD "—"
  let notesCell := if e.notes.isEmpty then "" else e.notes
  let cyclesCell := match e.cycleBound with
    | some n => s!"{n}"
    | none   => "—"
  s!"| {tierIcon e.tier} {e.name} | {tierLabel e.tier} | `{proofCell}` | {cyclesCell} | {notesCell} |"

private def renderRegistry : String :=
  let header :=
    "| Opcode | Tier | Witness theorem | Cycles (N) | Notes |\n\
     |---|---|---|---:|---|"
  let rows := String.intercalate "\n" (registry.map fmtRow)
  header ++ "\n" ++ rows

private def renderCounts : String :=
  s!"## Verification depth — A.2 opcode coverage

By **registry entry** (parameterized families collapsed; total = {totalEntries}):

| Tier | Count |
|---|---:|
| ✅ proven      | {provenCount} |
| 🔶 conditional | {conditionalCount} |
| 🟡 partial     | {partialCount} |
| ⏳ execSpec    | {execSpecCount} |
| ✗ notStarted   | {notStartedCount} |


By **opcode byte** (PUSH/DUP/SWAP/LOG families expanded; total = {totalBytes}):

| Tier | Bytes |
|---|---:|
| ✅ proven      | {provenBytes} |
| 🔶 conditional | {conditionalBytes} |
| 🟡 partial     | {partialBytes} |
| ⏳ execSpec    | {execSpecBytes} |
| ✗ notStarted   | {notStartedBytes} |
"

def main : IO Unit := do
  IO.println renderCounts
  IO.println ""
  IO.println "### Per-opcode registry"
  IO.println ""
  IO.println renderRegistry
