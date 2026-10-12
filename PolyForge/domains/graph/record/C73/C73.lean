import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C73 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 5) :
    2 * (G.minDegree : ℤ) ≤ 2 * (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) + 2 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
        have hw := connected_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.chromaticNumber.toNat : ℤ) ≥ -5 := by linarith [hn1]
      have s6 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s8 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s2, s7]
      have s9 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s8]) (by linarith [s6])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) ≥ -7 := by linarith [s2, s3, s4, s5, s9]
      have s11 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hr := s10; omega
      linarith [s11]
    · -- 1*chi <= 2
      have s12 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s13 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
        have hw := connected_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s16 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ -2 := by linarith [s12, s13, s14, s15]
      linarith [s16]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
