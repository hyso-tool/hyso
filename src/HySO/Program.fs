module HySO.Program

open Util
open FirstOrderModelChecking
open CommandLineParser

let run (args: string array) = 
    let swtotal = System.Diagnostics.Stopwatch()
    swtotal.Start()

    let config = SolverConfiguration.getSolverConfig()

    // Parse the command line args
    let cmdArgs =
        match CommandLineParser.parseCommandLineArguments (Array.toList args) with
            | Result.Ok x -> x
            | Result.Error e ->
                raise <| HySOException $"Could not parse commandline arguments: %s{e}"

    Util.DebugPrintouts <- cmdArgs.DebugOutputs
    
    // Check which method should be used, i.e., verify a program, verify a transition system
    let res = 
        match cmdArgs.ExecMode with 
            | ExplictSystem (systemPaths, propPath) -> 
                ModelCheckingEntryPoint.explictSystemVerification config systemPaths propPath 
            | INVALID -> 
                raise <| HySOException "Invalid command line arguments"

    match res with 
    | SAT, i -> 
        printfn "SAT"
        Util.LOGGERn $"Iterations: %i{i}"
    | UNSAT, i -> 
        printfn "UNSAT"
        Util.LOGGERn $"Iterations: %i{i}"
    | UNKNOWN, _ -> 
        printfn "UNKNOWN"

    swtotal.Stop()
    Util.LOGGERn $"Total Time %i{swtotal.ElapsedMilliseconds}ms (~=%.2f{double(swtotal.ElapsedMilliseconds) / 1000.0}s)\n\n"


[<EntryPoint>]
let main args =
    try 
        run args 
        0
    with 
    | HySOException err when Util.DEBUG ->
        printfn $"Error: %s{err}"
        reraise() 
    | _ when Util.DEBUG -> 
        reraise()
    | HySOException err -> 
        printfn $"Error: %s{err}"
        1
    | e -> 
        printfn $"General Error: %s{e.Message}"
        1
