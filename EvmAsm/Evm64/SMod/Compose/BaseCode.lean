/-
  EvmAsm.Evm64.SMod.Compose.BaseCode

  CodeReq handles and sub-block inclusion lemmas for the SMOD wrapper.
-/

import EvmAsm.Evm64.SMod.Compose.CodeHandles

namespace EvmAsm.Evm64.SMod.Compose

theorem smodCode_saveRa_sub {base : Word} :
    ∀ a i, (saveRaCode base) a = some i → (smodCode base) a = some i := by
  unfold saveRaCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + saveRaOff)
    EvmAsm.Evm64.evm_smod_legacy (EvmAsm.Evm64.evm_smod_save_ra_block .x18) 0
    (by simp [saveRaOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCode_dividendSign_sub {base : Word} :
    ∀ a i, (dividendSignCode base) a = some i → (smodCode base) a = some i := by
  unfold dividendSignCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendSignOff)
    EvmAsm.Evm64.evm_smod_legacy
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_smodDividendTopLimbOff) 1
    (by simp [dividendSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCode_preserveDividendSign_sub {base : Word} :
    ∀ a i, (preserveDividendSignCode base) a = some i → (smodCode base) a = some i := by
  unfold preserveDividendSignCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + preserveDividendSignOff)
    EvmAsm.Evm64.evm_smod_legacy (EvmAsm.Rv64.ADDI .x13 .x8 0) 3
    (by simp [preserveDividendSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCode_divisorSign_sub {base : Word} :
    ∀ a i, (divisorSignCode base) a = some i → (smodCode base) a = some i := by
  unfold divisorSignCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorSignOff)
    EvmAsm.Evm64.evm_smod_legacy
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_smodDivisorTopLimbOff) 4
    (by simp [divisorSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCode_dividendAbs_sub {base : Word} :
    ∀ a i, (dividendAbsCode base) a = some i → (smodCode base) a = some i := by
  unfold dividendAbsCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendAbsOff)
    EvmAsm.Evm64.evm_smod_legacy
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 6
    (by simp [dividendAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCode_divisorAbs_sub {base : Word} :
    ∀ a i, (divisorAbsCode base) a = some i → (smodCode base) a = some i := by
  unfold divisorAbsCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorAbsOff)
    EvmAsm.Evm64.evm_smod_legacy
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56) 27
    (by simp [divisorAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCode_modCall_sub {base : Word} :
    ∀ a i, (modCallCode base) a = some i → (smodCode base) a = some i := by
  unfold modCallCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + modCallOff)
    EvmAsm.Evm64.evm_smod_legacy
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_smodCallOff) 48
    (by simp [modCallOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCode_resultSignFix_sub {base : Word} :
    ∀ a i, (resultSignFixCode base) a = some i → (smodCode base) a = some i := by
  unfold resultSignFixCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + resultSignFixOff)
    EvmAsm.Evm64.evm_smod_legacy
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x13 .x10 .x7 .x11
      0 8 16 24) 49
    (by simp [resultSignFixOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCode_savedRaRet_sub {base : Word} :
    ∀ a i, (savedRaRetCode base) a = some i → (smodCode base) a = some i := by
  unfold savedRaRetCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + savedRaRetOff)
    EvmAsm.Evm64.evm_smod_legacy (EvmAsm.Evm64.evm_smod_saved_ra_ret_block .x18) 70
    (by simp [savedRaRetOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCode_modCallable_sub {base : Word} :
    ∀ a i, (modCallableCode base) a = some i → (smodCode base) a = some i := by
  unfold modCallableCode smodCode
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + wrapperEndOff)
    EvmAsm.Evm64.evm_smod_legacy EvmAsm.Evm64.evm_mod_callable_v1 71
    (by simp [wrapperEndOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)

theorem smodCodeV4_saveRa_sub {base : Word} :
    ∀ a i, (saveRaCode base) a = some i → (smodCodeV4 base) a = some i := by
  unfold saveRaCode smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + saveRaOff)
    EvmAsm.Evm64.evm_smod (EvmAsm.Evm64.evm_smod_save_ra_block .x18) 0
    (by simp [saveRaOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCodeV4_dividendSign_sub {base : Word} :
    ∀ a i, (dividendSignCode base) a = some i → (smodCodeV4 base) a = some i := by
  unfold dividendSignCode smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendSignOff)
    EvmAsm.Evm64.evm_smod
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x8
      EvmAsm.Evm64.evm_smodDividendTopLimbOff) 1
    (by simp [dividendSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCodeV4_preserveDividendSign_sub {base : Word} :
    ∀ a i, (preserveDividendSignCode base) a = some i → (smodCodeV4 base) a = some i := by
  unfold preserveDividendSignCode smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + preserveDividendSignOff)
    EvmAsm.Evm64.evm_smod (EvmAsm.Rv64.ADDI .x13 .x8 0) 3
    (by simp [preserveDividendSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCodeV4_divisorSign_sub {base : Word} :
    ∀ a i, (divisorSignCode base) a = some i → (smodCodeV4 base) a = some i := by
  unfold divisorSignCode smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorSignOff)
    EvmAsm.Evm64.evm_smod
    (EvmAsm.Evm64.evm_sdiv_sign_bit_block .x12 .x9
      EvmAsm.Evm64.evm_smodDivisorTopLimbOff) 4
    (by simp [divisorSignOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCodeV4_dividendAbs_sub {base : Word} :
    ∀ a i, (dividendAbsCode base) a = some i → (smodCodeV4 base) a = some i := by
  unfold dividendAbsCode smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + dividendAbsOff)
    EvmAsm.Evm64.evm_smod
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x8 .x10 .x7 .x11
      0 8 16 24) 6
    (by simp [dividendAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCodeV4_divisorAbs_sub {base : Word} :
    ∀ a i, (divisorAbsCode base) a = some i → (smodCodeV4 base) a = some i := by
  unfold divisorAbsCode smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + divisorAbsOff)
    EvmAsm.Evm64.evm_smod
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x9 .x10 .x7 .x11
      32 40 48 56) 27
    (by simp [divisorAbsOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCodeV4_modCall_sub {base : Word} :
    ∀ a i, (modCallCode base) a = some i → (smodCodeV4 base) a = some i := by
  unfold modCallCode smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + modCallOff)
    EvmAsm.Evm64.evm_smod
    (EvmAsm.Evm64.evm_sdiv_div_call_block EvmAsm.Evm64.evm_smodCallOff) 48
    (by simp [modCallOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCodeV4_resultSignFix_sub {base : Word} :
    ∀ a i, (resultSignFixCode base) a = some i → (smodCodeV4 base) a = some i := by
  unfold resultSignFixCode smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + resultSignFixOff)
    EvmAsm.Evm64.evm_smod
    (EvmAsm.Evm64.evm_sdiv_cond_negate_256_block .x12 .x13 .x10 .x7 .x11
      0 8 16 24) 49
    (by simp [resultSignFixOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCodeV4_savedRaRet_sub {base : Word} :
    ∀ a i, (savedRaRetCode base) a = some i → (smodCodeV4 base) a = some i := by
  unfold savedRaRetCode smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + savedRaRetOff)
    EvmAsm.Evm64.evm_smod (EvmAsm.Evm64.evm_smod_saved_ra_ret_block .x18) 70
    (by simp [savedRaRetOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCodeV4_modCallable_sub {base : Word} :
    ∀ a i, (modCallableCodeV4 base) a = some i → (smodCodeV4 base) a = some i := by
  unfold modCallableCodeV4 smodCodeV4
  exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base (base + wrapperEndOff)
    EvmAsm.Evm64.evm_smod EvmAsm.Evm64.evm_mod_callable_v4 71
    (by simp [wrapperEndOff])
    (by native_decide)
    (by native_decide)
    (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)

theorem smodCode_block_subs {base : Word} :
    (∀ a i, (saveRaCode base) a = some i → (smodCode base) a = some i) ∧
    (∀ a i, (dividendSignCode base) a = some i → (smodCode base) a = some i) ∧
    (∀ a i, (preserveDividendSignCode base) a = some i → (smodCode base) a = some i) ∧
    (∀ a i, (divisorSignCode base) a = some i → (smodCode base) a = some i) ∧
    (∀ a i, (dividendAbsCode base) a = some i → (smodCode base) a = some i) ∧
    (∀ a i, (divisorAbsCode base) a = some i → (smodCode base) a = some i) ∧
    (∀ a i, (modCallCode base) a = some i → (smodCode base) a = some i) ∧
    (∀ a i, (resultSignFixCode base) a = some i → (smodCode base) a = some i) ∧
    (∀ a i, (savedRaRetCode base) a = some i → (smodCode base) a = some i) ∧
    (∀ a i, (modCallableCode base) a = some i → (smodCode base) a = some i) := by
  exact ⟨smodCode_saveRa_sub, smodCode_dividendSign_sub,
    smodCode_preserveDividendSign_sub, smodCode_divisorSign_sub,
    smodCode_dividendAbs_sub, smodCode_divisorAbs_sub, smodCode_modCall_sub,
    smodCode_resultSignFix_sub, smodCode_savedRaRet_sub,
    smodCode_modCallable_sub⟩

theorem smodCodeV4_block_subs {base : Word} :
    (∀ a i, (saveRaCode base) a = some i → (smodCodeV4 base) a = some i) ∧
    (∀ a i, (dividendSignCode base) a = some i → (smodCodeV4 base) a = some i) ∧
    (∀ a i, (preserveDividendSignCode base) a = some i → (smodCodeV4 base) a = some i) ∧
    (∀ a i, (divisorSignCode base) a = some i → (smodCodeV4 base) a = some i) ∧
    (∀ a i, (dividendAbsCode base) a = some i → (smodCodeV4 base) a = some i) ∧
    (∀ a i, (divisorAbsCode base) a = some i → (smodCodeV4 base) a = some i) ∧
    (∀ a i, (modCallCode base) a = some i → (smodCodeV4 base) a = some i) ∧
    (∀ a i, (resultSignFixCode base) a = some i → (smodCodeV4 base) a = some i) ∧
    (∀ a i, (savedRaRetCode base) a = some i → (smodCodeV4 base) a = some i) ∧
    (∀ a i, (modCallableCodeV4 base) a = some i → (smodCodeV4 base) a = some i) := by
  exact ⟨smodCodeV4_saveRa_sub, smodCodeV4_dividendSign_sub,
    smodCodeV4_preserveDividendSign_sub, smodCodeV4_divisorSign_sub,
    smodCodeV4_dividendAbs_sub, smodCodeV4_divisorAbs_sub, smodCodeV4_modCall_sub,
    smodCodeV4_resultSignFix_sub, smodCodeV4_savedRaRet_sub,
    smodCodeV4_modCallable_sub⟩

/-- Canonical production-code block subsumptions for SMOD. -/
theorem smodCodeCanonical_block_subs {base : Word} :
    (∀ a i, (saveRaCode base) a = some i → (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (dividendSignCode base) a = some i → (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (preserveDividendSignCode base) a = some i →
      (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (divisorSignCode base) a = some i → (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (dividendAbsCode base) a = some i → (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (divisorAbsCode base) a = some i → (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (modCallCode base) a = some i → (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (resultSignFixCode base) a = some i → (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (savedRaRetCode base) a = some i → (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (modCallableCodeV4 base) a = some i →
      (smodCodeCanonical base) a = some i) := by
  simpa [smodCodeCanonical] using smodCodeV4_block_subs (base := base)

/-- Bundled top-level SMOD code subsumptions for the wrapper and appended
    legacy v1 unsigned MOD callable. -/
theorem smodCode_top_level_subs {base : Word} :
    (∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base EvmAsm.Evm64.evm_smod_wrapper) a = some i →
      (smodCode base) a = some i) ∧
    (∀ a i, (modCallableCode base) a = some i → (smodCode base) a = some i) := by
  constructor
  · intro a i h
    unfold smodCode
    exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base base
      EvmAsm.Evm64.evm_smod_legacy EvmAsm.Evm64.evm_smod_wrapper 0
      (by simp)
      (by unfold EvmAsm.Evm64.evm_smod_legacy; simp only [EvmAsm.Rv64.seq, EvmAsm.Rv64.Program]; rfl)
      (by rw [EvmAsm.Evm64.evm_smod_legacy_length, EvmAsm.Evm64.evm_smod_wrapper_length]; norm_num)
      (by rw [EvmAsm.Evm64.evm_smod_legacy_length]; norm_num)
      a i h
  · exact smodCode_modCallable_sub

/-- Bundled top-level SMOD v4 code subsumptions for the wrapper and appended
    v4 unsigned MOD callable. -/
theorem smodCodeV4_top_level_subs {base : Word} :
    (∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base EvmAsm.Evm64.evm_smod_wrapper) a = some i →
      (smodCodeV4 base) a = some i) ∧
    (∀ a i, (modCallableCodeV4 base) a = some i → (smodCodeV4 base) a = some i) := by
  constructor
  · intro a i h
    unfold smodCodeV4
    exact EvmAsm.Rv64.CodeReq.ofProg_mono_sub base base
      EvmAsm.Evm64.evm_smod EvmAsm.Evm64.evm_smod_wrapper 0
      (by simp)
      (by unfold EvmAsm.Evm64.evm_smod; simp only [EvmAsm.Rv64.seq, EvmAsm.Rv64.Program]; rfl)
      (by rw [EvmAsm.Evm64.evm_smod_length, EvmAsm.Evm64.evm_smod_wrapper_length]; norm_num)
      (by rw [EvmAsm.Evm64.evm_smod_length]; norm_num)
      a i h
  · exact smodCodeV4_modCallable_sub

/-- Bundled top-level SMOD code subsumptions for the canonical production
    wrapper and appended v4 unsigned MOD callable. -/
theorem smodCodeCanonical_top_level_subs {base : Word} :
    (∀ a i, (EvmAsm.Rv64.CodeReq.ofProg base EvmAsm.Evm64.evm_smod_wrapper) a = some i →
      (smodCodeCanonical base) a = some i) ∧
    (∀ a i, (modCallableCodeV4 base) a = some i →
      (smodCodeCanonical base) a = some i) := by
  simpa [smodCodeCanonical] using smodCodeV4_top_level_subs (base := base)

end EvmAsm.Evm64.SMod.Compose
