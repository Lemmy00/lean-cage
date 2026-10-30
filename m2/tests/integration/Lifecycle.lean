import LeanCageM2

-- §AR-lifecycle.proofs: Executable failure/race fixtures supplement universal invariants.
namespace LeanCageM2.Tests
open LeanCageM2 LeanCage.Linux.Filter

private def run (events : List Event) : Option State :=
  replay nativeAbi canonicalBytes initial events

private def errno22 : LeanCage.Launch.Errno := ⟨22, by decide⟩

#guard wirePlan == "12345678"
#guard match preparePlan nativeAbi canonicalBytes with
  | .ok operations => operations == plan
  | .error _ => false
#guard (preparePlan nativeAbi ByteArray.empty).isOk == false
#guard run successEvents == some successState
#guard run [.ok .exec] == none
#guard run [.ok .namespaces] == none
#guard run [.ok .bootstrap, .ok .handles] == none
#guard run (successEvents.reverse) == none

-- §AR-lifecycle.proofs: Every partial setup can fail/interupt/violate its effect contract.
#guard plan.all fun op =>
  let before := (setupPrefix op).map Event.ok
  (run (before ++ [.setupError op errno22])).map State.phase == some .failed
#guard plan.all fun op =>
  (run ((setupPrefix op).map Event.ok ++ [.interrupted op])).map State.phase == some .failed
#guard plan.all fun op =>
  (run ((setupPrefix op).map Event.ok ++ [.contractViolation op])).map State.phase == some .failed
#guard plan.all fun op =>
  run ((setupPrefix op).map Event.ok ++ [.setupError op errno22, .ok .exec]) == none

-- §AR-lifecycle.proofs: Cancellation request admits the real exec race until observed death.
#guard (run (.cancelRequest :: successEvents)).map State.entered == some true
#guard (run (successEvents ++ [.cancelRequest])).map State.extinct == some false
#guard (run (successEvents ++ [.cancelRequest, .namespaceDeath])).map State.extinct == some true
#guard (run (successEvents ++ [.namespaceDeath, .ok .exec])) == none
#guard (run (successEvents ++ [.reportLost])).map State.knowledge == some .unknown
#guard (run (successEvents ++ [.reportLost])).map State.entered == some true

-- §AR-lifecycle.proofs: No borrowed handle or unowned process becomes a cleanup target.
#guard run [.release 10] == none
#guard (run (successEvents ++ [.release 99])) == none
#guard (run (successEvents ++ [.namespaceDeath, .release 10])).map State.released == some [10]
#guard (run (successEvents ++ [.namespaceDeath, .release 10, .release 10])) == none
#guard (run (successEvents ++ [.fork ⟨2,1,restrictedCredentials,true,true⟩ 2])) == none
#guard (run (successEvents ++ [.fork ⟨9,2,{},false,false⟩ 3])) == none
#guard (run (successEvents ++ [.fork ⟨2,1,restrictedCredentials,true,true⟩ 3,
    .escapeAttempt ⟨3,1,restrictedCredentials,true,true⟩, .signalOutside ⟨3,1,restrictedCredentials,true,true⟩,
    .namespaceDeath])).map State.members == some []

-- §AR-lifecycle.proofs: General bytecode proof also has concrete boundary/fuel checks.
#guard Bytecode.run Program.denyGetppid.instructions 0xc000003e 110 10 0 0 == some 0x50001
#guard Bytecode.run Program.denyGetppid.instructions 0xc000003e 0x3fffffff 10 0 0 == some 0x7fff0000
#guard Bytecode.run Program.denyGetppid.instructions 0xc000003e 0x40000000 10 0 0 == some 0x80000000
#guard Bytecode.run Program.denyGetppid.instructions 0x40000003 39 10 0 0 == some 0x80000000
#guard Bytecode.run #[] 0 0 10 0 0 == none
#guard Bytecode.run #[⟨0x20,0,0,8⟩] 0 0 10 0 0 == none
#guard Bytecode.run #[⟨0x15,255,255,0⟩] 0 0 10 0 0 == none
#guard Bytecode.run #[⟨6,0,0,0x7fff0000⟩] 0 0 0 0 0 == none

end LeanCageM2.Tests
