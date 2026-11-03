import LeanCageEntry.Worker

-- §AR-entry.caller: The shipped entry image rejects every nonproduction selector.
def main (args : List String) : IO UInt32 := LeanCage.Entry.Worker.run false args
