import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C6 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ 2 * (G.edgeFinset.card : ℤ)) :
    2 * (G.minDegree : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) - 2 := by
  have s1 : -2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by
    by_cases hc1 : (2 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 2
      have s2 : -2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by
        by_cases hc2 : (1 : ℤ) ≤ (G.edgeFinset.card : ℤ)
        · -- 1*m >= 1
          have s3 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
            have hw := omega_le_chi_int G
            linarith [hw]
          have s4 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            linarith [hw]
          have s5 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            linarith [hw]
          have s6 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hcc := hc2; omega
          have s7 : -2 * (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
          have s8 : -2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by linarith [s3, s4, s5, s6, s7]
          linarith [s8]
        · -- 1*m <= 0
          have s9 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            linarith [hw]
          have s10 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
            have hw := max_le_edges_int G
            linarith [hw]
          have s11 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            linarith [hw]
          have s12 : (G.cliqueNum : ℤ) ≥ 1 := by
            have hw := omega_ge_one_int' G
            linarith [hw]
          have s13 : -(G.edgeFinset.card : ℤ) ≥ 0 := by have hcc := hc2; omega
          have s14 : -2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by linarith [s9, s10, s11, s12, s13]
          linarith [s14]
      linarith [s2]
    · -- 1*n <= 1
      have s15 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        linarith [hw]
      have s16 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        linarith [hw]
      have s17 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        linarith [hw]
      have s18 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int' G
        linarith [hw]
      have s19 : -(Fintype.card V : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s20 : -2 * (G.minDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by linarith [s15, s16, s17, s18, s19]
      linarith [s20]
  linarith [s1]
