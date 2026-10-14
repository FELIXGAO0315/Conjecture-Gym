import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C58 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≥ 2 * (G.indepNum : ℤ)) (hn2 : (G.girth : ℤ) ≤ 5) :
    (G.vertexCoverNum.toNat : ℤ) ≥ (G.girth : ℤ) - 1 := by
  have s1 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
    have hw := girth_le_card_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : -2 * (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(G.girth : ℤ) ≥ -5 := by linarith [hn2]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s5 : 3 * (Fintype.card V : ℤ) - 3 * (G.indepNum : ℤ) - 3 * (G.girth : ℤ) ≥ -5 := by linarith [s1, s2, s3, s4]
  have s6 : (Fintype.card V : ℤ) - (G.indepNum : ℤ) - (G.girth : ℤ) ≥ -1 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
