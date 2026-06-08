/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS
import ArkLib.Data.CodingTheory.ProximityGap.AHIV22

noncomputable section

/-!
# Issue #141 — the GS-exposed MCA error obeys the proven proximity gap in the unique-decoding regime

This file lands an **unconditional, axiom-clean** bound: for Reed–Solomon codes and *any* GS list
family `L`, the GS-exposed mutual-correlated-agreement error — restricted to the non-jointly-close
stacks, the `ε_ca` convention — is bounded in the unique-decoding regime by the **proven**
BCIKS20/AHIV17 proximity-gap error `errorBound δ deg α = n/q`.

It is the composition of two proven results, with no new hypothesis:

* `ProximityGap.MCAGS.epsMCAgs_restricted_le_epsCA` — the restricted GS-exposed error is `≤ ε_ca`
  (the GS analogue of `epsMCA_restricted_le_epsCA`, proven via the line-close domination);
* `ProximityToRS.ahiv17_epsCA_bound_uniqueDecodingRegime` — in the UDR `δ ≤ relUDR(RS)`, the
  correlated-agreement error `ε_ca ≤ errorBound = n/q` (the BCIKS20 unique-decoding proximity gap).

This certifies that the GS-exposed MCA framework is *sound against the classical proximity gap*
where the latter is proven. It is **not** the prize bound: `n/q` is the proximity-gap shape,
incomparable to the prize's `poly(2^m,1/ρ)/q` shape (the prize needs the GS list-size form, valid
only beyond the proximity-gap regime up to capacity — the open ABF26 core). Tracking: Issue #141.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

namespace MCAGS

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Finite F] [DecidableEq F]

local instance : Fintype F := Fintype.ofFinite F

open Classical in
/-- **The GS-exposed MCA error obeys the proven proximity gap in UDR (unconditional, axiom-clean).**
For Reed–Solomon codes and *any* GS list family `L`, in the unique-decoding regime
`δ ≤ relUDR(RS)`, the restricted GS-exposed MCA error is `≤ errorBound δ deg α = n/q`, the proven
BCIKS20 unique-decoding proximity gap. Pure composition of `epsMCAgs_restricted_le_epsCA` and
`ahiv17_epsCA_bound_uniqueDecodingRegime`; no new hypothesis, no `axiom`, no `sorry`. -/
theorem epsMCAgs_restricted_le_errorBound_udr
    (deg : ℕ) (α : ι ↪ F)
    (L : WordStack F (Fin 2) ι → Finset (ι → F)) {δ : ℝ≥0}
    (hδ : δ ≤ Code.relativeUniqueDecodingRadius
      (C := (↑(ReedSolomon.code α deg) : Set (ι → F)))) :
    (⨆ u : WordStack F (Fin 2) ι,
      if jointProximity (C := (ReedSolomon.RScodeSet α deg)) (u := u) δ then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[mcaEventGSrow (L u) (ReedSolomon.RScodeSet α deg) δ (u 0) (u 1) γ])
      ≤ (ProximityGap.errorBound δ deg α : ENNReal) :=
  le_trans
    (epsMCAgs_restricted_le_epsCA (F := F) (A := F) (ReedSolomon.RScodeSet α deg) δ L)
    (ProximityToRS.ahiv17_epsCA_bound_uniqueDecodingRegime
      (ι := ι) (F := F) (deg := deg) (α := α) hδ)

/-! ## Source audit -/

#print axioms ProximityGap.MCAGS.epsMCAgs_restricted_le_errorBound_udr

end MCAGS

end ProximityGap

end
