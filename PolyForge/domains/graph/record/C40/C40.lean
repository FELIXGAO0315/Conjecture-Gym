import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C40 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.edgeFinset.card : ℤ) ≤ 3) :
    (G.chromaticNumber.toNat : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) := by
  have s1 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    by_cases hc1 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : -(G.edgeFinset.card : ℤ) ≥ -3 := by linarith [hn1]
      have s5 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*n <= 2
      have s6 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s7 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s10 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s11 : 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ (2 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s10]) (by linarith [s9])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : 3 * (Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 2 := by linarith [s6, s7, s8, s11]
      linarith [s12]
  linarith [s1]
