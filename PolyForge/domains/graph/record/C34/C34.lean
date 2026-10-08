import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C34 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0) (hn2 : (G.maxDegree : ℤ) ≤ 3) :
    -(Fintype.card V : ℤ) + 2 * (G.minDegree : ℤ) ≤ 2 := by
  have s1 : (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        linarith [hw]
      have s3 : -(G.maxDegree : ℤ) ≥ -3 := by linarith [hn2]
      have s4 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s5 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s6 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s4, s5]
      have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int G (by omega)
        linarith [hw]
      have s8 : (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ -2 := by linarith [s2, s3, s7]
      linarith [s8]
    · -- 1*chi <= 2
      have s9 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        linarith [hw]
      have s11 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        linarith [hw]
      have s12 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s14 : (Fintype.card V : ℤ) - 2 * (G.minDegree : ℤ) ≥ -2 := by linarith [s9, s10, s11, s12, s13]
      linarith [s14]
  linarith [s1]
