import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C240 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (Fintype.card V : ℤ) ≤ 5) :
    (G.edgeFinset.card : ℤ) ≤ 3 * (G.indepNum : ℤ) - 2 := by
  have s1 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
    have hw := bipartite_four_mul_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s5 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
  have s6 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 5 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (Fintype.card V : ℤ)) :=
      mul_nonneg (by linarith [s4]) (by linarith [s5])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s8 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s7]) (by linarith [s1])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s9 : -4 * (G.edgeFinset.card : ℤ) + 12 * (G.indepNum : ℤ) ≥ 5 := by linarith [s1, s2, s3, s6, s8]
  have s10 : -(G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by have hr := s9; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s10, heq_gallai]
