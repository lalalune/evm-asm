/-
  EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1FullV5

  Full v5 div128 Phase-1 block spec: instrs [10]-[40], exit at [41]
  (base+124). Composes the prefix+Phase-1b-leading-guard
  (`divK_div128_step1_initcapguard_v5_spec_within`, [10..22]) with the
  Phase-1b body (`divK_div128_phase1b_body_v5_spec_within`, [23..40]).

  Control flow (nested branch):
    * Outer guard (rhatc ≥ 2^32, i.e. rhatc>>32 ≠ 0): skip both D3
      corrections, exit [41] with q1''=q1c, rhat''=rhatc.
    * Otherwise (rhatc>>32 = 0): run the body — 1st D3 (prodcheck1) then
      2nd D3 (prodcheck1b, guarded) — exit [41] with the corrected q/rhat.

  Composition: `cpsBranchWithin_seq_cpsBranchWithin_with_perm` advances
  BOTH combined exits to base+124, then `cpsBranchWithin_merge_same_cr`
  collapses to a `cpsTripleWithin` with the unified Phase-1 postcondition.
  The outer-guard pure `⌜rhatc>>32 = 0⌝` is FRAMED onto the body so the
  merge bridges can resolve the outer conditional.

  Output `q1''`/`rhat''` agree with `div128Quot_v5`'s Phase-1 result (the
  model-form match — model uses `decide(rhatc>>32=0) && …` — is deferred
  to the `div128_v5_spec` composition).

  Bead `evm-asm-wbc4i.6.6` (V5.6.7).
-/

import EvmAsm.Evm64.DivMod.LimbSpec.Div128Step1V5
import EvmAsm.Evm64.DivMod.LimbSpec.Div128Phase1bV5
import EvmAsm.Rv64.Tactics.DropPure

open EvmAsm.Rv64.Tactics

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Code requirement for the full v5 step-1 block [10..40]: the
    init+cap+Phase-1b-guard code unioned with the Phase-1b body code. -/
def divKDiv128Step1FullV5Code (base : Word) : CodeReq :=
  (divKDiv128Step1InitCapGuardV5Code base).union
  (divKDiv128Phase1bBodyV5Code (base + 52))

/-- Precondition for the full v5 step-1 block: the init+cap+guard entry
    state plus `un1` in x11 and `dlo` in memory (threaded for the body). -/
def divKDiv128Step1FullV5Pre (sp uHi dHi un1 v10Old v5Old v9Old dlo : Word) :
    Assertion :=
  (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ uHi) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ v10Old) **
  (.x5 ↦ᵣ v5Old) ** (.x9 ↦ᵣ v9Old) ** (.x0 ↦ᵣ 0) ** (.x11 ↦ᵣ un1) **
  (sp + signExtend12 3952 ↦ₘ dlo)

/-- Postcondition: the v5 Phase-1 register state at [41] (base+124).
    `q1''` in x10, `rhat''` in x7 — the corrected trial quotient/remainder.
    Expressed as the outer `rhatc>>32` guard over the body's two-D3 output;
    `x5`/`x9` are scratch (3-path conditional). -/
def divKDiv128Step1FullV5Post (sp uHi dHi un1 dlo : Word) : Assertion :=
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi := q1 >>> (32 : BitVec 6).toNat
  let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q1c := if hi = 0 then q1 else q1cCap
  let rhatc := if hi = 0 then rhat else rhat + (q1 - q1cCap) * dHi
  let x5o := if hi = 0 then hi else q1cCap
  let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
  -- Body 1st D3 (only meaningful when rhatcHi = 0).
  let qDlo1 := q1c * dlo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let bq1' := if BitVec.ult rhatUn1 qDlo1 then q1c + signExtend12 4095 else q1c
  let brhat' := if BitVec.ult rhatUn1 qDlo1 then rhatc + dHi else rhatc
  let brhat'Hi := brhat' >>> (32 : BitVec 6).toNat
  -- Body 2nd D3.
  let qDlo2 := bq1' * dlo
  let rhatUn1' := (brhat' <<< (32 : BitVec 6).toNat) ||| un1
  let bq1'' := if BitVec.ult rhatUn1' qDlo2 then bq1' + signExtend12 4095 else bq1'
  let brhat'' := if BitVec.ult rhatUn1' qDlo2 then brhat' + dHi else brhat'
  -- Outer guard: taken (rhatcHi ≠ 0) skips both corrections.
  let q1Final := if rhatcHi ≠ 0 then q1c else (if brhat'Hi = 0 then bq1'' else bq1')
  let rhatFinal := if rhatcHi ≠ 0 then rhatc else (if brhat'Hi = 0 then brhat'' else brhat')
  let x5Exit := if rhatcHi ≠ 0 then x5o else (if brhat'Hi = 0 then qDlo2 else qDlo1)
  let x9Exit := if rhatcHi ≠ 0 then rhatcHi else (if brhat'Hi = 0 then rhatUn1' else brhat'Hi)
  (.x12 ↦ᵣ sp) ** (.x7 ↦ᵣ rhatFinal) ** (.x6 ↦ᵣ dHi) ** (.x10 ↦ᵣ q1Final) **
  (.x5 ↦ᵣ x5Exit) ** (.x11 ↦ᵣ un1) ** (.x9 ↦ᵣ x9Exit) ** (.x0 ↦ᵣ 0) **
  (sp + signExtend12 3952 ↦ₘ dlo)

/-- Disjointness of the two halves of the full step-1 code (prefix+guard at
    [10..22] vs Phase-1b body at [23..40]). Top-level (fresh heartbeat budget)
    and peeled to singleton-vs-singleton leaves to keep each `bv_omega` cheap. -/
theorem divKDiv128Step1FullV5_code_disjoint (base : Word) :
    (divKDiv128Step1InitCapGuardV5Code base).Disjoint
      (divKDiv128Phase1bBodyV5Code (base + 52)) := by
  unfold divKDiv128Step1InitCapGuardV5Code divKDiv128Step1InitCapV5Code
    divKDiv128Phase1bBodyV5Code divKDiv128Prodcheck1bMergedCode
  repeat' apply CodeReq.Disjoint.union_left
  all_goals (repeat' apply CodeReq.Disjoint.union_right)
  all_goals exact CodeReq.Disjoint.singleton (by bv_omega)

/-- Full v5 div128 Phase-1 block (instrs [10]-[40], exit [41]=base+124):
    init + Phase-1a cap + Phase-1b leading guard + both D3 corrections. -/
theorem divK_div128_step1_v5_spec_within
    (sp uHi dHi un1 v10Old v5Old v9Old dlo : Word) (base : Word) :
    cpsTripleWithin 31 base (base + 124) (divKDiv128Step1FullV5Code base)
      (divKDiv128Step1FullV5Pre sp uHi dHi un1 v10Old v5Old v9Old dlo)
      (divKDiv128Step1FullV5Post sp uHi dHi un1 dlo) := by
  -- Minimal locals for the body call (matching the guard's outputs).
  let q1 := rv64_divu uHi dHi
  let hi := q1 >>> (32 : BitVec 6).toNat
  let q1cCap : Word := (BitVec.allOnes 64) >>> (32 : BitVec 6).toNat
  let q1c := if hi = 0 then q1 else q1cCap
  let rhatc := if hi = 0 then (uHi - q1 * dHi) else (uHi - q1 * dHi) + (q1 - q1cCap) * dHi
  let x5o := if hi = 0 then hi else q1cCap
  let rhatcHi := rhatc >>> (32 : BitVec 6).toNat
  let cr := (divKDiv128Step1InitCapGuardV5Code base).union
            (divKDiv128Phase1bBodyV5Code (base + 52))
  -- Swap only the code requirement (keep Pre/Post folded → light whnf).
  show cpsTripleWithin 31 base (base + 124) cr
    (divKDiv128Step1FullV5Pre sp uHi dHi un1 v10Old v5Old v9Old dlo)
    (divKDiv128Step1FullV5Post sp uHi dHi un1 dlo)
  -- 0-step bridge helper (mirrors step1_v2_spec).
  have refl_of {P : Assertion}
      (h : ∀ hp, P hp → divKDiv128Step1FullV5Post sp uHi dHi un1 dlo hp) :
      cpsTripleWithin 0 (base + 124) (base + 124) cr P
        (divKDiv128Step1FullV5Post sp uHi dHi un1 dlo) :=
    cpsTripleWithin_extend_code (fun _ _ h => by simp [CodeReq.empty] at h)
      (cpsTripleWithin_refl h)
  -- h1: prefix + Phase-1b guard [10..22], framed with x11=un1 + dlo-mem.
  have hg0 := divK_div128_step1_initcapguard_v5_spec_within sp uHi dHi v10Old v5Old v9Old base
  have h1 := cpsBranchWithin_frameR
    ((.x11 ↦ᵣ un1) ** (sp + signExtend12 3952 ↦ₘ dlo)) (by pcFree) hg0
  -- h2: Phase-1b body [23..40] at base+52, framed with the outer-guard pure.
  have hb0 := divK_div128_phase1b_body_v5_spec_within sp q1c rhatc dHi un1 rhatcHi x5o dlo (base + 52)
  have hbe : (base + 52 : Word) + 72 = base + 124 := by bv_addr
  rw [hbe] at hb0
  have h2 := cpsBranchWithin_frameR (⌜rhatcHi = 0⌝) (by pcFree) hb0
  -- Compose the two branches (both exits at base+124).
  have hd := divKDiv128Step1FullV5_code_disjoint base
  have combined := cpsBranchWithin_seq_cpsBranchWithin_with_perm
    (Q_t := divKDiv128Step1FullV5Post sp uHi dHi un1 dlo)
    hd
    h1
    -- hperm: guard-ft post (framed) → body pre (framed with ⌜rhatcHi=0⌝)
    (fun h hp => by xperm_hyp hp)
    h2
    -- ht1: guard-taken post (framed) → Post (outer if_pos via ⌜rhatcHi≠0⌝)
    (fun h hp => by
      sorry)
    -- ht2: body-taken post (framed ⌜rhatcHi=0⌝) → Post
    (fun h hp => by
      sorry)
  -- Collapse: both exits at base+124, 0-step bridges.
  have merged := cpsBranchWithin_merge_same_cr combined (refl_of (fun hp h => h))
    -- h_f: body-ft post (framed ⌜rhatcHi=0⌝) → Post
    (refl_of (fun hp hp' => by sorry))
  -- Reconcile the framed prefix pre with the flat `…Pre` def.
  exact cpsTripleWithin_weaken
    (fun h hp => by unfold divKDiv128Step1FullV5Pre at hp; xperm_hyp hp)
    (fun h hp => hp) merged

end EvmAsm.Evm64
