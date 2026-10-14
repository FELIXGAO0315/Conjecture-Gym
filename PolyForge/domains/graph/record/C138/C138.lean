import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C138 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : ¬ G.IsAcyclic) (hn1 : (G.diam : ℤ) ≤ (G.girth : ℤ)) :
    (G.diam : ℤ) ≤ (G.radius.toNat : ℤ) + 3 * (G.girth : ℤ) - 8 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp2
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.diam : ℤ) + (G.girth : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : -2 * (G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) + 6 * (G.girth : ℤ) ≥ 15 := by linarith [s1, s2, s3]
  have s5 : -(G.diam : ℤ) + (G.radius.toNat : ℤ) + 3 * (G.girth : ℤ) ≥ 8 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
