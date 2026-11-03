import LeanCageEntry.Program

namespace LeanCage.Entry.Linux

-- §AR-entry.effects: Native fallback is ENOSYS; no theorem assumes the foreign call succeeds.
@[extern "leancage_entry_primitive"]
def primitive (_op : UInt32) (_a _b _c : UInt64) (_text : @& String)
    (_args : @& Array String) (_data : @& ByteArray) : BaseIO Reply :=
  pure (0 - 38, .empty)

def call (request : Request) : BaseIO Reply :=
  primitive request.op.code request.a request.b request.c request.text request.args request.data

end LeanCage.Entry.Linux
