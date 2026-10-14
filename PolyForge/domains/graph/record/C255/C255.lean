import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C255 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 3) (hn2 : (Fintype.card V : ℤ) ≥ 2 * (G.indepNum : ℤ)) :
    (G.vertexCoverNum.toNat : ℤ) ≥ 3 * (G.chromaticNumber.toNat : ℤ) - 7 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [hn1]
  have s3 : (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : 2 * (Fintype.card V : ℤ) - 6 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.indepNum : ℤ) ≥ -15 := by linarith [s1, s2, s3]
  have s5 : (Fintype.card V : ℤ) - 3 * (G.chromaticNumber.toNat : ℤ) - (G.indepNum : ℤ) ≥ -7 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
