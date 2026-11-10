import SnapshotProofs.Copy
import LeanCageHost.Json.Unicode

namespace LeanCage.Host.Snapshot

open Filesystem

theorem nameOfBytes_provenance (bytes : ByteArray) (name : String)
    (accepted : nameOfBytes bytes = .ok name) :
    bytes.size ≤ 255 ∧ name.toUTF8 = bytes ∧
      (name = "." ∨ name = ".." ∨ ValidComponent name) := by
  unfold nameOfBytes at accepted
  split at accepted
  · cases accepted
  · rename_i bounded
    split at accepted
    · cases accepted
    · rename_i text decoded
      split at accepted
      · rename_i allowed
        cases accepted
        exact ⟨by omega, (Json.strict_utf8 decoded).2, allowed⟩
      · cases accepted

structure NamesValid (remaining : Nat) (seen names : List String) : Prop where
  bounded : names.length ≤ remaining
  unique : names.Nodup
  seen : ∀ name ∈ names, name ∈ seen
  components : ∀ name ∈ names, ValidComponent name

-- §FS-host-boundary.snapshot: Nonprogress, errors and loss cannot grow an unbounded cursor loop.
theorem enumerate_prefix_bound (fuel : Nat) (cursor : UInt64) (remaining : Nat)
    (seen names : List String) {events : List (Request × Option Reply)}
    (run : Prefix (enumerate fuel cursor remaining seen names) events) : events.length ≤ fuel := by
  induction fuel generalizing seen names events with
  | zero =>
    have empty := prefix_pure_empty run
    simp [empty]
  | succ fuel ih =>
    simp only [enumerate] at run
    cases run with
    | empty => simp
    | lost => simp
    | returned request next reply tail rest =>
      dsimp only at rest
      split at rest
      · have empty := prefix_pure_empty rest
        simp [empty]
      · split at rest
        · have empty := prefix_pure_empty rest
          simp [empty]
        · split at rest
          · have empty := prefix_pure_empty rest
            simp [empty]
          · split at rest
            · have empty := prefix_pure_empty rest
              simp [empty]
            · split at rest
              · have bound := ih _ _ rest
                simp only [List.length_cons]
                omega
              · split at rest
                · have empty := prefix_pure_empty rest
                  simp [empty]
                · have bound := ih _ _ rest
                  simp only [List.length_cons]
                  omega

-- §FS-host-boundary.snapshot: Bounds and decoded-name uniqueness precede the sorting call.
theorem enumerate_provenance (fuel : Nat) (cursor : UInt64) (remaining : Nat)
    (seen names : List String) (valid : NamesValid remaining seen names)
    {events : List (Request × Reply)} {found : List String}
    (run : Returns (enumerate fuel cursor remaining seen names) events (.ok found)) :
    found.length ≤ remaining ∧ found.Nodup ∧ ∀ name ∈ found, ValidComponent name := by
  induction fuel generalizing seen names events found with
  | zero => cases run
  | succ fuel ih =>
    simp only [enumerate] at run
    obtain ⟨reply, rest, rfl, tail⟩ := returns_call_split run
    split at tail
    · obtain ⟨rfl, equal⟩ := returns_pure_eq tail
      cases equal
      exact ⟨by simpa using valid.bounded,
        List.pairwise_reverse.mpr (valid.unique.imp (fun different => Ne.symm different)),
        by simpa using valid.components⟩
    · split at tail
      · cases tail
      · split at tail
        · cases tail
        · rename_i name recognized
          have meaning := (nameOfBytes_provenance _ _ recognized).2.2
          split at tail
          · cases tail
          · rename_i fresh
            split at tail
            · have next : NamesValid remaining (name :: seen) names :=
                ⟨valid.bounded, valid.unique,
                  by intro item member; exact .tail _ (valid.seen item member), valid.components⟩
              exact ih _ _ next tail
            · rename_i nonDot
              split at tail
              · cases tail
              · rename_i room
                have component : ValidComponent name := by
                  rcases meaning with dot | dot | component
                  · exact False.elim (nonDot (.inl dot))
                  · exact False.elim (nonDot (.inr dot))
                  · exact component
                have next : NamesValid remaining (name :: seen) (name :: names) := by
                  refine ⟨by simpa only [List.length_cons] using (show names.length + 1 ≤ remaining by omega),
                    List.nodup_cons.mpr ⟨?_, valid.unique⟩, ?_, ?_⟩
                  · intro present
                    exact fresh (valid.seen name present)
                  · intro item present
                    simp only [List.mem_cons] at present
                    rcases present with rfl | old
                    · exact .head _
                    · exact .tail _ (valid.seen item old)
                  · intro item present
                    simp only [List.mem_cons] at present
                    rcases present with rfl | old
                    · exact component
                    · exact valid.components item old
                exact ih _ _ next tail

theorem sorted_names_provenance (fuel : Nat) (cursor : UInt64) (remaining : Nat)
    {events : List (Request × Reply)} {names : List String}
    (run : Returns (enumerate fuel cursor remaining [] []) events (.ok names)) :
    (sortNames names).length ≤ remaining ∧ (sortNames names).Nodup ∧
      ∀ name ∈ sortNames names, ValidComponent name := by
  obtain ⟨bounded, unique, components⟩ := enumerate_provenance fuel cursor remaining [] []
    ⟨by simp, by simp, by simp, by simp⟩ run
  have permutation := List.mergeSort_perm names (fun a b => bytesLE a.toUTF8.data.toList b.toUTF8.data.toList)
  exact ⟨by simpa [sortNames] using bounded, permutation.nodup_iff.mpr unique,
    by intro name present; exact components name (permutation.mem_iff.mp present)⟩

end LeanCage.Host.Snapshot
