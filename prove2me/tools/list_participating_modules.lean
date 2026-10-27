import QPBT.Palomar.PauliCompleteness
import QPBT.Palomar.LowDegreeSoundness
import QPBT.Palomar.PauliSoundness

open Lean

run_meta do
  let env ← getEnv
  let modules := env.header.moduleNames.toList
    |>.filter (fun name => `QPBT |>.isPrefixOf name)
    |>.mergeSort Name.lt
    |>.map (·.toString)
  IO.FS.writeFile "prove2me/extracted/participating-modules.txt"
    (String.intercalate "\n" modules ++ "\n")
  logInfo s!"wrote {modules.length} participating modules"
