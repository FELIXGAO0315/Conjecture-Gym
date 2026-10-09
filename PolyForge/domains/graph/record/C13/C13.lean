import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C13 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsAcyclic) (hp2 : G.Connected) (hn1 : (Fintype.card V : ℤ) ≥ 1) :
    (G.vertexCoverNum.toNat : ℤ) ≤ (Fintype.card V : ℤ) + 2 * (G.radius.toNat : ℤ) - 3 := by
  have s1 : -(G.diam : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 0 := by
    have hw := diam_le_two_radius_int G hp2
    linarith [hw]
  have s2 : 2 * (G.diam : ℤ) - (G.girth : ℤ) ≥ -1 := by
    have hw := girth_le_diam_int G hp2 hp1
    linarith [hw]
  have s3 : (G.girth : ℤ) ≥ 3 := by
    have hw := girth_ge_three_int G hp1
    linarith [hw]
  have s4 : 2 * (G.radius.toNat : ℤ) ≥ 1 := by linarith [s1, s2, s3]
  have s5 : (G.radius.toNat : ℤ) ≥ 1 := by have hr := s4; omega
  have s6 : (Fintype.card V : ℤ) ≥ 1 := by linarith [hn1]
  have s7 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
    have hw := tau_le_card_sub_one_int G (by omega)
    linarith [hw]
  have s8 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) + 2 * (G.radius.toNat : ℤ) ≥ 3 := by linarith [s5, s7]
  linarith [s8]
