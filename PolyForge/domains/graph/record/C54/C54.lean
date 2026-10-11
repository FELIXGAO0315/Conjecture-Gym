import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C54 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)) (hn2 : (G.cliqueNum : ℤ) ≤ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    (Fintype.card V : ℤ) ≥ -(G.maxDegree : ℤ) + 3 := by
  have s1 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s5 : 2 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 6 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s7 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s9 : 2 * (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [s6, s7, s8]
      have s10 : (G.edgeFinset.card : ℤ) ≥ 1 := by have hr := s9; omega
      have s11 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s12 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s13 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s14 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s12, s13]
      have s15 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s16 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s17 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s6, s15, s8, s16]
      have s18 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s17; omega
      have s19 : 2 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s18]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s20 : 2 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) ≥ 6 := by linarith [s10, s11, s19]
      linarith [s20]
  linarith [s1]
