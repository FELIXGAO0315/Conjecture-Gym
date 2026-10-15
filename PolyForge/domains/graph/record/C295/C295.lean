import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C295 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ 2 * (G.maxDegree : ℤ)) :
    2 * (G.maxDegree : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) - 3 := by
  have s1 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    by_cases hc1 : (2 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 2
      have s2 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
        by_cases hc2 : (1 : ℤ) ≤ (G.maxDegree : ℤ)
        · -- 1*max_deg >= 1
          have s3 : (G.maxDegree : ℤ) ≥ 1 := by have hcc := hc2; omega
          have s4 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
          have s5 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by linarith [s3, s4]
          linarith [s5]
        · -- 1*max_deg <= 0
          have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            try push_cast at hw
            linarith [hw]
          have s7 : -(G.maxDegree : ℤ) ≥ 0 := by have hcc := hc2; omega
          have s8 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s6, s7]
          linarith [s8]
      linarith [s2]
    · -- 1*n <= 1
      have s9 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : -(Fintype.card V : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s12 : -2 * (G.maxDegree : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s9, s10, s11]
      linarith [s12]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
