import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C53 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsEdgeConnected 1) (hp2 : 2 ≤ Fintype.card V) (hn1 : (G.edgeFinset.card : ℤ) ≥ 3) :
    (Fintype.card V : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) := by
  have s1 : -(Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ 0 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [hn1]
      have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.minDegree : ℤ) ≥ 1 := by
        have hw := edge_conn_min_deg_int G hp1 hp2
        try push_cast at hw
        linarith [hw]
      have s5 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s5, s6]
      have s8 : -(Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -3 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s7]) (by linarith [s4])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : -(Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ 0 := by linarith [s2, s3, s8]
      linarith [s9]
    · -- 1*chi <= 2
      have s10 : -(Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ 0 := by
        by_cases hc10 : (4 : ℤ) ≤ (Fintype.card V : ℤ)
        · -- 1*n >= 4
          have s11 : (G.minDegree : ℤ) ≥ 1 := by
            have hw := edge_conn_min_deg_int G hp1 hp2
            try push_cast at hw
            linarith [hw]
          have s12 : (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [hn1]
          have s13 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
            have hw := handshake_min_int G
            try push_cast at hw
            linarith [hw]
          have s14 : (Fintype.card V : ℤ) ≥ 4 := by have hcc := hc10; omega
          have s15 : -(Fintype.card V : ℤ) - 4 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -4 := by
            have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 4) * ((G.minDegree : ℤ) - 1) :=
              mul_nonneg (by linarith [s14]) (by linarith [s11])
            ring_nf at hmul ⊢
            linarith [hmul]
          have s16 : -(Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ 0 := by linarith [s11, s12, s13, s15]
          linarith [s16]
        · -- 1*n <= 3
          have s17 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
            have hw := min_le_max_int G
            try push_cast at hw
            linarith [hw]
          have s18 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
            have hw := max_lt_card_int' G
            try push_cast at hw
            linarith [hw]
          have s19 : (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [hn1]
          have s20 : -(Fintype.card V : ℤ) ≥ -3 := by have hcc := hc10; omega
          have s21 : -(Fintype.card V : ℤ) + 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) ≥ 0 := by linarith [s17, s18, s19, s20]
          linarith [s21]
      linarith [s10]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
