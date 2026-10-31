import LeanCageM3

open LeanCageM3
-- §AR-workspace.proofs: Pure checks exercise counterexamples and boundaries; proofs are audited
-- separately.
#guard readHandle usefulAuthority 3 == none
#guard readHandle (openName usefulAuthority [97] 3 false) 3 == some [65]
#guard readHandle (writeHandle (openName usefulAuthority [97] 3 false) 3 [66]) 3 == some [65]
#guard readHandle (closeHandle (openName usefulAuthority [97] 3 true) 3) 3 == none
#guard readHandle (dupHandle (openName usefulAuthority [97] 3 true) 3 4) 4 == some [65]
#guard readHandle (setName (openName usefulAuthority [97] 3 true) [97] none) 3 == some [65]
#guard resolve (fun _ => some (.symlink [97])) 40 [97] == none
#guard resolve (fun _ => some (.object ⟨1, 1⟩)) 0 [97] == none
#guard (writeHandle usefulAuthority 3 [90]).objects 7 == usefulAuthority.objects 7
#guard (allocateObject usefulAuthority 7 2 [90]).objects 7 == usefulAuthority.objects 7
#guard (allocateObject usefulAuthority 8 2 [90]).objects 8 == some ⟨2, .workspace 1, [90]⟩
#guard readable 1 (.workspace 2) == false
#guard readable 1 .outside == false
#guard readable 1 .runtime == true
#guard writable 1 .runtime == false
#guard (launchStep {} .attemptExec).entered == false
#guard (launchStep { receipts := required, failed := true } .attemptExec).entered == false
#guard (observe {} .cancel).extinct == false
#guard (observe {} .releaseObserved).released == false
#guard (observe { extinct := true } .releaseObserved).released == true
#guard (observe { entry := .yes } .reportLost).entry == .yes
#guard (observe {} .reportLost).entry == .unknown
#guard (sample {} 100 1 0 100 100).cpuCancel == true
#guard (sample {} 1 100 0 100 100).wallCancel == true
#guard (sample { lastCPU := 100 } 99 1 0 1000 1000).accountingLost == true
#guard (sample {} 1 1 0 1000 1000).oomObserved == false
#guard (sample {} 1 1 1 1000 1000).oomObserved == true
#guard admitTask 4 4 == 4
#guard admitTask 3 4 == 4
#guard capturePrefix 2 [1] [2, 3] == [1, 2]
#guard nextRun 18446744073709551615 == none
#guard reusable ⟨1, false, false, true⟩ == false
#guard Filter.action 0xc000003e 435 0 0 == Filter.fallback
#guard Filter.action 0xc000003e 56 0x10000011 0 == Filter.deny
#guard Filter.action 0xc000003e 56 17 1 == Filter.deny
#guard Filter.action 0xc000003e 56 17 0 == Filter.allow
#guard Filter.action 0xc000003e 41 0 0 == Filter.deny
#guard Filter.action 0xc000003e 0x40000027 0 0 == Filter.kill
#guard Filter.action 0x40000003 0 0 0 == Filter.kill
#guard (decodeResult ByteArray.empty).isOk == false
#guard (StrictJson.parse "{\"x\":1,\"x\":2}".toUTF8).isOk == false
#guard (StrictJson.parse "{\"x\":1e2}".toUTF8).isOk == false
#guard (StrictJson.parse "{\"x\":18446744073709551616}".toUTF8).isOk == false
#guard (StrictJson.parse "{\"x\":01}".toUTF8).isOk == false
#guard (StrictJson.parse "{\"x\":\"\\u0000\"}".toUTF8).isOk == false
#guard (StrictJson.parse "{\"x\":1,}".toUTF8).isOk == false
#guard (StrictJson.parse "[] []".toUTF8).isOk == false

-- §AR-workspace.transport: Exact public-frame length and reserved fields, including every truncated
-- prefix.
def putWord (bytes : ByteArray) (offset width value : Nat) : ByteArray :=
  (List.range width).foldl (fun b i => b.set! (offset + i) (UInt8.ofNat (value / 2 ^ (8 * i)))) bytes

def goodFrame : ByteArray := Id.run do
  let mut b := ByteArray.mk (Array.replicate 160 0)
  for (offset, width, value) in [(0,4,0x5233434c),(4,2,1),(8,8,1),(24,4,128),(40,4,1),(44,4,1),(52,4,100000)] do
    b := putWord b offset width value
  return b

#guard (decodeResult goodFrame).isOk
#guard (List.range 160).all (fun n => !(decodeResult (goodFrame.extract 0 n)).isOk)
#guard !(decodeResult (goodFrame.push 0)).isOk
#guard !(decodeResult (putWord goodFrame 0 1 0)).isOk
#guard !(decodeResult (putWord goodFrame 4 2 2)).isOk
#guard !(decodeResult (putWord goodFrame 6 2 6)).isOk
#guard !(decodeResult (putWord goodFrame 8 8 0)).isOk
#guard !(decodeResult (putWord goodFrame 16 8 1)).isOk
#guard !(decodeResult (putWord goodFrame 24 4 65537)).isOk
#guard !(decodeResult (putWord goodFrame 28 4 1)).isOk
#guard !(decodeResult (putWord goodFrame 32 4 8)).isOk
#guard !(decodeResult (putWord goodFrame 36 4 256)).isOk
#guard !(decodeResult (putWord goodFrame 40 4 0)).isOk
#guard !(decodeResult (putWord goodFrame 44 4 2)).isOk
#guard !(decodeResult (putWord goodFrame 48 4 64)).isOk
#guard !(decodeResult (putWord goodFrame 52 4 0)).isOk
#guard !(decodeResult (putWord goodFrame 96 4 4)).isOk
#guard !(decodeResult (putWord goodFrame 104 1 1)).isOk
#guard !(decodeResult (putWord goodFrame 156 1 1)).isOk

-- §AR-workspace.proofs: Raw handle operations agree after issuance; guessed inherited handles are
-- cleared.
#guard readIssued (openName usefulAuthority [97] 3 true) 3 == some [65]
#guard readIssued (writeIssued (openName usefulAuthority [97] 3 true) 3 [66]) 3 == some [66]
#guard readIssued (writeIssued (openName usefulAuthority [97] 3 false) 3 [66]) 3 == some [65]
#guard reserve 100 50 150 == some 150
#guard reserve 100 51 150 == none
#guard reserve 151 0 150 == none

-- §AR-workspace.transport: A missing measurement must never become an apparent zero-cost result.
def reportPolicy : Policy := ⟨#["/bin/sh"], none, none, false,
  ⟨16777216, 4, 100000, 100000, 10000, 100, 1048576, 64, 0, 64, 64⟩⟩
def faultReport (trigger : Nat) : Lean.Json :=
  let frame := putWord (putWord (putWord (putWord goodFrame 6 2 4) 32 4 9) 36 4 71) 48 4 trigger
  match decodeResult frame with
  | .error _ => Lean.Json.null
  | .ok result => detailedReport result reportPolicy Lean.Json.null
#guard ((faultReport 16).getObjVal? "cpu_usage_us").toOption.any Lean.Json.isNull
#guard ((faultReport 16).getObjVal? "cpu_observed_overshoot_us").toOption.any Lean.Json.isNull
#guard ((faultReport 16).getObjVal? "elapsed_ms").toOption.any Lean.Json.isNull
#guard ((faultReport 8).getObjVal? "stdout_captured_bytes").toOption.any Lean.Json.isNull
#guard ((faultReport 8).getObjVal? "stdout_truncated").toOption.any Lean.Json.isNull
