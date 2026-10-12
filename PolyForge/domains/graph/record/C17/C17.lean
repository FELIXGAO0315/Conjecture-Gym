import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C17 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 6) :
    3 * (Fintype.card V : ℤ) ≥ (G.edgeFinset.card : ℤ) + 3 := by
  have s1 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
    have hw := two_mul_edges_le_card_sq_sub_card_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) ≥ -6 := by linarith [hn1]
  have s4 : 7 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 6 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (6 - (Fintype.card V : ℤ)) :=
      mul_nonneg (by linarith [s2]) (by linarith [s3])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s5 : 3 * (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) ≥ 3 := by linarith [s1, s4]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
