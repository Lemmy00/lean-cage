import LeanCageEntry.Worker

-- §AR-entry.acceptance: Only the explicitly named test image enables injected setup failures.
def main (args : List String) : IO UInt32 := LeanCage.Entry.Worker.run true args
