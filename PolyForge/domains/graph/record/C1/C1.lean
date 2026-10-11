import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C1 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≥ 2 * (G.maxDegree : ℤ)) (hn2 : (G.minDegree : ℤ) ≤ 1) :
    2 * (G.maxDegree : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) - 2 := by
  have s1 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : -2 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s4 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 3 := by linarith [s2, s3]
      linarith [s4]
    · -- 1*chi <= 2
      have s5 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by
        by_cases hc5 : (2 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 2
          have s6 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by
            by_cases hc6 : (1 : ℤ) ≤ (G.maxDegree : ℤ)
            · -- 1*max_deg >= 1
              have s7 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
                have hw := omega_le_chi_int G
                linarith [hw]
              have s8 : (G.maxDegree : ℤ) ≥ 1 := by have hcc := hc6; omega
              have s9 : -2 * (G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
              have s10 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by linarith [s7, s8, s9]
              linarith [s10]
            · -- 1*max_deg <= 0
              have s11 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
                have hw := chi_ge_one_int' G
                linarith [hw]
              have s12 : (G.cliqueNum : ℤ) ≥ 1 := by
                have hw := omega_ge_one_int' G
                linarith [hw]
              have s13 : -(G.maxDegree : ℤ) ≥ 0 := by have hcc := hc6; omega
              have s14 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by linarith [s11, s12, s13]
              linarith [s14]
          linarith [s6]
        · -- 1*n <= 1
          have s15 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            linarith [hw]
          have s16 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
            have hw := chi_ge_one_int' G
            linarith [hw]
          have s17 : (G.cliqueNum : ℤ) ≥ 1 := by
            have hw := omega_ge_one_int' G
            linarith [hw]
          have s18 : -(Fintype.card V : ℤ) ≥ -1 := by have hcc := hc5; omega
          have s19 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by linarith [s15, s16, s17, s18]
          linarith [s19]
      linarith [s5]
  linarith [s1]
