import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C128 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ)) :
    (G.girth : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) - 2 := by
  have s1 : (Fintype.card V : ℤ) ≥ 3 := by
    have hw := three_le_card_of_cycle_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.girth : ℤ) ≥ 0 := by
    have hw := girth_le_card_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : -(Fintype.card V : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 6 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.girth : ℤ) ≥ 3 := by linarith [s1, s2, s3]
  have s5 : 3 * (G.chromaticNumber.toNat : ℤ) - (G.girth : ℤ) ≥ 2 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
