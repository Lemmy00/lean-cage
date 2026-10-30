import LeanCage.Linux.Launch
import LeanCage.Proofs.FilterDecoder
import LeanCage.Proofs.Launch

namespace LeanCage.Linux

open Filter

-- §FS-filter-loading.installation.model: The actual decoder, not a supplied premise, gates setup.
theorem validationVerdict_iff (abi : Abi) (bytes : ByteArray) (entryAccepted : Bool) :
    validationVerdict abi bytes entryAccepted = true ↔
      ValidInput abi bytes ∧ entryAccepted = true := by
  cases hd : decode abi bytes with
  | error error =>
    have hn : ¬ ValidInput abi bytes := by
      intro hv
      have hs := decode_complete hv
      simp [hd] at hs
    simp [validationVerdict, hd, hn]
  | ok program => simp [validationVerdict, hd, decode_success hd]

-- §FS-filter-loading.installation.model: Any invalid input excludes guest entry on every trace.
theorem invalid_input_never_executes (abi : Abi) (bytes : ByteArray) (entryAccepted : Bool)
    (trace : Launch.Trace) (h : ¬ ValidInput abi bytes) :
    Launch.replay (validationVerdict abi bytes entryAccepted) .unvalidated trace ≠
      some .executed := by
  have hv : validationVerdict abi bytes entryAccepted = false := by
    cases he : validationVerdict abi bytes entryAccepted
    · rfl
    · exact False.elim (h ((validationVerdict_iff abi bytes entryAccepted).mp he).1)
  rw [hv]
  exact Launch.rejected_never_executes trace

-- §FS-filter-loading.installation.binding: Every prepared native input satisfies the byte spec.
theorem prepared_filter_valid (prepared : PreparedFilter) : ValidInput nativeAbi prepared.bytes :=
  decode_success prepared.accepted

-- §FS-filter-loading.installation.model: Decoder and full success trace are jointly inhabited.
theorem decoded_success_witness :
    Launch.replay (validationVerdict nativeAbi canonicalBytes true)
      .unvalidated Launch.successTrace = some .executed := by
  rfl

end LeanCage.Linux
