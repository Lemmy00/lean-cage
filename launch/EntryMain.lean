import LeanCageEntry.Worker

-- §AR-entry.caller: The shipped entry image rejects every nonproduction selector.
def main (args : List String) : IO UInt32 := LeanCage.Entry.Worker.run false args

-- §AR-entry.caller: Bind the actual production entrypoint to the proved worker and selector.
theorem production_main_calls_worker (args : List String) :
    main args = LeanCage.Entry.Worker.run false args := rfl
