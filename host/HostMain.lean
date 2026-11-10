import LeanCageHost.Entrypoint

open LeanCage.Host

-- §FS-host-boundary.caller: Interpret the same complete program whose phases are verified.
def main : IO UInt32 := Entrypoint.run.interpret
