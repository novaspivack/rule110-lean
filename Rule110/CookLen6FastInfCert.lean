import Rule110.CookLen6TailEvolution

/-!
# L=6 fast bounded list certificates (Stage 3, Phase A)

List-only `native_decide` checks for the chunked `390 + 30 → 420` simulation at slot origins.
These certificates avoid `InfTape`/`infRule110Steps` unfolding entirely.

**Discharged:** `c2SimRun 420` at each slot origin equals `c2SimRun 30` after the post-390 evolved list.

**Pending InfTape lift:** `len6_evolved_inf30_eq_list420_at_slot` in `CookLen6InfTapeBridge` — the
`n = 390` list↔InfTape bridge on the 30-step read cone exceeds Lean's default elaborator heartbeat
budget; the Python script `papers/30_cook_theorem/scripts/len6_evolved_origin_cert.py` mirrors the
list certificates for independent verification.
-/

namespace Rule110

/-- Alias: fast list compose certificate at slot origins (`M₁ = 390`, `M₂ = 30`). -/
abbrev len6FastCompose420OriginOk : Bool := len6Tail420ComposeOriginOk

theorem len6_fast_compose420_origin_ok : len6FastCompose420OriginOk = true := by
  simpa [len6FastCompose420OriginOk] using len6_tail420_compose_origin_ok

theorem len6_fast_compose420_origin_get (slot : ℕ) (hslot : slot < 6) :
    (c2SimRun 420 len6TruePhasedSupportInit).getD (c2SimOrigin slot) false =
      (c2SimRun 30 len6TailEvolvedList).getD (c2SimOrigin slot) false :=
  len6_tail420_compose_evolved_get slot hslot

end Rule110
