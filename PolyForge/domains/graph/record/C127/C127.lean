import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C127 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 6) :
    (G.chromaticNumber.toNat : ℤ) ≤ 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - 2 := by
  have s1 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.edgeFinset.card : ℤ) ≥ -6 := by linarith [hn1]
      have s6 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s7 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.maxDegree : ℤ) ≥ -6 := by linarith [s7, s5]
      have s9 : 6 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 18 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (6 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s6]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : 9 * (Fintype.card V : ℤ) - 3 * (G.edgeFinset.card : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by linarith [s2, s3, s4, s5, s9]
      have s11 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s10; omega
      linarith [s11]
    · -- 1*n <= 2
      have s12 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s15 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s16 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s17 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s18 : 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ (2 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s17]) (by linarith [s16])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s19 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s12, s13, s14, s15, s18]
      linarith [s19]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
