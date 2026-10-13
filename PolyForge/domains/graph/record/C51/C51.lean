import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C51 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.minDegree : ℤ) ≥ 1) :
    2 * (G.cliqueNum : ℤ) ≤ 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 3 := by
  have s1 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.minDegree : ℤ)
    · -- 1*min_deg >= 2
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
        have hw := not_bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s5 : (G.minDegree : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s6 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s8 : -2 * (Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 2) :=
          mul_nonneg (by linarith [s7]) (by linarith [s5])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [s3, s4, s5, s6, s8]
      have s10 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s3, s4]
      have s11 : -2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -6 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 2) :=
          mul_nonneg (by linarith [s10]) (by linarith [s5])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by linarith [s2, s3, s9, s6, s11]
      linarith [s12]
    · -- 1*min_deg <= 1
      have s13 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
        have hw := not_bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s16 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s17 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.minDegree : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s19 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s20 : (G.minDegree : ℤ) ≥ 1 := by linarith [hn1]
      have s21 : -(Fintype.card V : ℤ) - (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ -1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * ((G.minDegree : ℤ) - 1) :=
          mul_nonneg (by linarith [s19]) (by linarith [s20])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s22 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 4 * (G.cliqueNum : ℤ) ≥ -7 := by linarith [s13, s14, s15, s16, s17, s18, s21]
      have s23 : 3 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ -3 := by have hr := s22; omega
      linarith [s23]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
