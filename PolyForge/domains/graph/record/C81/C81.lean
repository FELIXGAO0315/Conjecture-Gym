import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C81 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 6) :
    2 * (G.edgeFinset.card : ℤ) ≥ 2 * (G.minDegree : ℤ) + (G.cliqueNum : ℤ) - 2 := by
  have s1 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
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
      have s5 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s6 : -(G.chromaticNumber.toNat : ℤ) ≥ -6 := by linarith [hn1]
      have s7 : -(G.cliqueNum : ℤ) ≥ -6 := by linarith [s5, s6]
      have s8 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s9 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s11 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s9, s10]
      have s12 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s11]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : 6 * (G.edgeFinset.card : ℤ) - 6 * (G.minDegree : ℤ) - 3 * (G.cliqueNum : ℤ) ≥ -8 := by linarith [s2, s3, s4, s7, s12]
      have s14 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -2 := by have hr := s13; omega
      linarith [s14]
    · -- 1*chi <= 2
      have s15 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s16 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s17 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s19 : 2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -2 := by linarith [s15, s16, s17, s18]
      linarith [s19]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
