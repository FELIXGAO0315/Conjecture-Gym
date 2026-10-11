import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C12 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.vertexCoverNum.toNat : ℤ)) :
    (G.indepNum : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s4 : 2 * (Fintype.card V : ℤ) - 2 * (G.indepNum : ℤ) ≥ 1 := by linarith [s1, s2, s3]
  have s5 : (Fintype.card V : ℤ) - (G.indepNum : ℤ) ≥ 1 := by have hr := s4; omega
  linarith [s5]
