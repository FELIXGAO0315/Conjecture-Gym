import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C235 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.Connected) (hn1 : (G.edgeFinset.card : ℤ) ≥ 6) :
    (G.chromaticNumber.toNat : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 5 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
    by_cases hc1 : (5 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 5
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
        have hw := connected_edges_int G hp2
        try push_cast at hw
        linarith [hw]
      have s4 : (G.edgeFinset.card : ℤ) ≥ 6 := by linarith [hn1]
      have s5 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.minDegree : ℤ) ≥ 1 := by
        have hw := connected_min_deg_int G hp2 hp1
        try push_cast at hw
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) ≥ 5 := by have hcc := hc1; omega
      have s8 : -(Fintype.card V : ℤ) - 5 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -5 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 5) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s7]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s2, s3, s4, s5, s8]
      linarith [s9]
    · -- 1*n <= 4
      have s10 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s13 : (G.edgeFinset.card : ℤ) ≥ 6 := by linarith [hn1]
      have s14 : -(Fintype.card V : ℤ) ≥ -4 := by have hcc := hc1; omega
      have s15 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 5 := by linarith [s10, s11, s12, s13, s14]
      linarith [s15]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
