import Cache.Hashing

open Lean Cache IO Hashing

def main (args : List String) : IO Unit := CacheM.run do
  let roots ← parseArgs ("lookup" :: args)
  let memo ← getHashMemo roots
  for (name, _) in roots.toList do
    let some hash := memo.hashMap[name]?
      | throw <| IO.userError s!"missing hash for {name}"
    IO.println s!"{name} {hash.asLTar}"
