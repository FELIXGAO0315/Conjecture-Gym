import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C40 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.minDegree : ℤ) ≤ 5) :
    2 * (G.edgeFinset.card : ℤ) ≥ 3 * (G.minDegree : ℤ) - 2 * (G.indepNum : ℤ) + 1 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 1 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s5 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s7 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s5, s6]
      have s8 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s7]) (by linarith [s4])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 2 := by linarith [s2, s3, s8]
      linarith [s9]
    · -- 1*chi <= 2
      have s10 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s11 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s13 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s14 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s16 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s15]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : 2 * (G.edgeFinset.card : ℤ) - 3 * (G.minDegree : ℤ) + 2 * (G.indepNum : ℤ) ≥ 1 := by linarith [s10, s11, s12, s13, s14, s16]
      linarith [s17]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
