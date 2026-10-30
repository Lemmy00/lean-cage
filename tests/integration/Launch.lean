import LeanCage

-- §AR-m1-launch.model: Exercise outcomes and ordering of the actual executable transition model.
namespace LeanCage.Tests.Launch

open LeanCage.Launch LeanCage.Linux LeanCage.Linux.Filter

private def einval : Errno := ⟨22, by decide⟩
private def eintr : Errno := ⟨4, by decide⟩

#guard replay true .unvalidated successTrace == some .executed
#guard replay false .unvalidated successTrace == none
#guard replay false .unvalidated [.failed .validationRejected] ==
  some (.failed .validationRejected)
#guard replay true .unvalidated [.noNewPrivilegesSet] == none
#guard replay true .unvalidated [.validationAccepted, .filterInstalled] == none
#guard replay true .unvalidated [.validationAccepted, .noNewPrivilegesSet, .execAttempted] == none
#guard replay true .unvalidated [.validationAccepted, .noNewPrivilegesSet,
  .filterInstalled, .execSucceeded] == none
#guard replay true .unvalidated [.validationAccepted, .noNewPrivilegesSet,
  .filterInstalled, .filterInstalled] == none

-- §AR-m1-launch.model: Every active success prefix can be cancelled or terminated.
#guard (List.range 5).all fun count =>
  replay true .unvalidated (successTrace.take count ++ [.failed .cancelled]) ==
    some (.failed .cancelled)
#guard (List.range 5).all fun count =>
  replay true .unvalidated (successTrace.take count ++ [.terminated]) == some .terminated

#guard replay true .unvalidated [.validationAccepted,
  .failed (.osError .setNoNewPrivileges einval)] ==
  some (.failed (.osError .setNoNewPrivileges einval))
#guard replay true .unvalidated [.validationAccepted, .noNewPrivilegesSet,
  .failed (.osError .installFilter einval)] == some (.failed (.osError .installFilter einval))
#guard replay true .unvalidated [.validationAccepted, .noNewPrivilegesSet,
  .failed (.interrupted .installFilter)] == some (.failed (.interrupted .installFilter))
#guard step true .privilegesRestricted (.failed (.osError .installFilter eintr)) == none
#guard step true .ready (.failed (.osError .exec einval)) == none
#guard step true .executing (.failed (.contractViolation .exec)) ==
  some (.failed (.contractViolation .exec))
#guard step true (.failed (.osError .installFilter einval)) .execAttempted == none
#guard step true .terminated .execAttempted == none
#guard step true .executed .execSucceeded == none

-- §AR-m1-launch.model: Real decoder results and platform checks jointly gate successful replay.
#guard validationVerdict nativeAbi canonicalBytes true
#guard !(validationVerdict nativeAbi canonicalBytes false)
#guard !(validationVerdict nativeAbi (canonicalBytes.set! 0 0) true)
#guard replay (validationVerdict nativeAbi canonicalBytes true) .unvalidated successTrace ==
  some .executed

end LeanCage.Tests.Launch
