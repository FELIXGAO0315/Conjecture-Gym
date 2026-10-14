import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C262 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.diam : ℤ) ≤ 5) :
    (G.maxDegree : ℤ) ≥ 3 * (G.diam : ℤ) - (G.radius.toNat : ℤ) - 10 := by
  have s1 : (G.maxDegree : ℤ) - 3 * (G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ -10 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.maxDegree : ℤ)
    · -- 1*max_deg >= 2
      have s2 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G hp1
        try push_cast at hw
        linarith [hw]
      have s3 : (G.maxDegree : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s4 : -(G.diam : ℤ) ≥ -5 := by linarith [hn1]
      have s5 : 2 * (G.maxDegree : ℤ) - 6 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ -21 := by linarith [s2, s3, s4]
      have s6 : (G.maxDegree : ℤ) - 3 * (G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ -10 := by have hr := s5; omega
      linarith [s6]
    · -- 1*max_deg <= 1
      have s7 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := diam_le_two_radius_int G hp1
        try push_cast at hw
        linarith [hw]
      have s8 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
        have hw := connected_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s9 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G hp1
        try push_cast at hw
        linarith [hw]
      have s10 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s11 : -(G.maxDegree : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s12 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s13 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : 2 * (G.maxDegree : ℤ) - 6 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ -3 := by linarith [s7, s8, s9, s10, s11, s13]
      have s15 : (G.maxDegree : ℤ) - 3 * (G.diam : ℤ) + (G.radius.toNat : ℤ) ≥ -1 := by have hr := s14; omega
      linarith [s15]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
