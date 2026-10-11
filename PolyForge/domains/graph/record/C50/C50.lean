import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C50 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.cliqueNum : ℤ) ≤ 4) (hn2 : (Fintype.card V : ℤ) ≥ 2 * (G.maxDegree : ℤ)) :
    (G.edgeFinset.card : ℤ) ≥ (G.minDegree : ℤ) + (G.cliqueNum : ℤ) - 2 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.cliqueNum : ℤ) ≥ -4 := by linarith [hn1]
      have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s7 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s8 : (Fintype.card V : ℤ) - 2 * (G.maxDegree : ℤ) ≥ 0 := by linarith [hn2]
      have s9 : (Fintype.card V : ℤ) ≥ 4 := by linarith [s7, s3, s8]
      have s10 : -4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s9]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s11 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -5 := by linarith [s2, s3, s4, s5, s10]
      have s12 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -2 := by have hr := s11; omega
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
      have s16 : (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -2 := by linarith [s13, s14, s15]
      linarith [s16]
  linarith [s1]
