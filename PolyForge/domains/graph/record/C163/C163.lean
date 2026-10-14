import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C163 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≥ (G.maxDegree : ℤ)) (hn2 : (G.minDegree : ℤ) ≤ 5) :
    2 * (G.minDegree : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - 3 * (G.cliqueNum : ℤ) + 7 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.cliqueNum : ℤ) ≥ -7 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.maxDegree : ℤ) + (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
      have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s9 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s7, s8, s4]
      have s10 : (G.minDegree : ℤ) ≥ 2 := by linarith [s8, s4, s6]
      have s11 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 2) :=
          mul_nonneg (by linarith [s9]) (by linarith [s10])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.cliqueNum : ℤ) ≥ -7 := by linarith [s2, s3, s4, s5, s6, s11]
      linarith [s12]
    · -- 1*omega <= 2
      have s13 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s16 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 3 * (G.cliqueNum : ℤ) ≥ -6 := by linarith [s13, s14, s15]
      linarith [s16]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
