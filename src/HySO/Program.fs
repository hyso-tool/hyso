module HySO.Program

open Util
open Configuration
open FirstOrderModelChecking
open CommandLineParser

let mutable raiseExceptions = false

let run (args: string array) = 
    let swtotal = System.Diagnostics.Stopwatch()
    swtotal.Start()

    let solverConfig = Configuration.getSolverConfig()

    // Parse the command line args
    let cmdArgs =
        match CommandLineParser.parseCommandLineArguments (Array.toList args) with
            | Result.Ok x -> x
            | Result.Error e ->
                raise <| HySOException $"Could not parse commandline arguments: %s{e}"

    let logger = 
        {
            Logger.Log =
                fun s ->
                    if cmdArgs.LogPrintouts then
                        printf $"%s{s}"
        }

    let config =
        {
            Configuration.SolverConfig = solverConfig
            Logger = logger
                
            RaiseExceptions = cmdArgs.RaiseExceptions
        }

    raiseExceptions <- cmdArgs.RaiseExceptions
    
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
        config.Logger.LogN $"Iterations: %i{i}"
    | UNSAT, i -> 
        printfn "UNSAT"
        config.Logger.LogN $"Iterations: %i{i}"
    | UNKNOWN, _ -> 
        printfn "UNKNOWN"

    swtotal.Stop()
    config.Logger.LogN $"Total Time %i{swtotal.ElapsedMilliseconds}ms (~=%.2f{double(swtotal.ElapsedMilliseconds) / 1000.0}s)\n\n"


[<EntryPoint>]
let main args =
    try 
        run args 
        0
    with
    | HySOException err ->
        printfn "=========== HySO ERROR ==========="
        printfn $"{err}"
        printfn "============================="

        if raiseExceptions then
            reraise ()

        -1
    | e ->
        printfn "=========== ERROR ==========="
        printfn $"{e.Message}"
        printfn "============================="

        if raiseExceptions then
            reraise ()

        -1
