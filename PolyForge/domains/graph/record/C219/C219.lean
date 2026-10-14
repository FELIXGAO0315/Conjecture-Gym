import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C219 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.Connected) (hn1 : (G.indepNum : ℤ) ≥ (G.vertexCoverNum.toNat : ℤ)) :
    (G.diam : ℤ) ≥ -(G.indepNum : ℤ) + (G.girth : ℤ) := by
  have s1 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
    have hw := girth_le_diam_int G hp2 hp1
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
    have hw := girth_le_card_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s5 : 2 * (G.indepNum : ℤ) + 2 * (G.diam : ℤ) - 2 * (G.girth : ℤ) ≥ -1 := by linarith [s1, s2, s3, s4]
  have s6 : (G.indepNum : ℤ) + (G.diam : ℤ) - (G.girth : ℤ) ≥ 0 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
