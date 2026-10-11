import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C2 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.cliqueNum : ℤ) ≥ 2 * (G.edgeFinset.card : ℤ)) :
    2 * (G.maxDegree : ℤ) ≤ (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) - 2 := by
  have s1 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by
    by_cases hc1 : (2 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 2
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        linarith [hw]
      have s3 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        linarith [hw]
      have s4 : (Fintype.card V : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s5 : -2 * (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s6 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        linarith [hw]
      have s7 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by linarith [s2, s3, s4, s5, s6]
      linarith [s7]
    · -- 1*n <= 1
      have s8 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        linarith [hw]
      have s9 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        linarith [hw]
      have s10 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int' G
        linarith [hw]
      have s11 : -(Fintype.card V : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s12 : -2 * (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 2 := by linarith [s8, s9, s10, s11]
      linarith [s12]
  linarith [s1]
