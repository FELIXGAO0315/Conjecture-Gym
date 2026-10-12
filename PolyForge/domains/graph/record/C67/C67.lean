import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C67 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hp2 : G.IsRegularOfDegree 3) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 6) :
    (G.chromaticNumber.toNat : ℤ) ≥ -(G.indepNum : ℤ) + 5 := by
  have s1 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s5 : -(G.chromaticNumber.toNat : ℤ) ≥ -6 := by linarith [hn1]
  have s6 : (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (6 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : (G.maxDegree : ℤ) = 3 := by
    have hw := regular_max_int' G hp2
    try push_cast at hw
    linarith [hw]
  have s8 : 6 * (G.maxDegree : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) + 6 * (G.indepNum : ℤ) ≥ 43 := by linarith [s1, s2, s3, s6, s7]
  have s9 : (G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ 8 := by have hr := s8; omega
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp2
  have heq_regx := regular_max_int' G hp2
  have heq_regn := regular_min_int' G hp2
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s9, heq_gallai, heq_rege, heq_regx, heq_regn]
