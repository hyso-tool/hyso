(*    
    Copyright (C) 2023-2024 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module HySO.Program

open Util
open Configuration
open FirstOrderModelChecking
open CommandLineParser

let mutable raiseExceptions = false

let sw = System.Diagnostics.Stopwatch()

let run (args : string array) =
    let swtotal = System.Diagnostics.Stopwatch()
    swtotal.Start()

    let solverConfig = Configuration.getSolverConfig ()

    // Parse the command line args
    let cmdArgs =
        match CommandLineParser.parseCommandLineArguments (Array.toList args) with
        | Result.Ok x -> x
        | Result.Error e -> raise <| HySOException $"Could not parse commandline arguments: %s{e}"

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
            PrintWitness = cmdArgs.PrintWitness

            RaiseExceptions = cmdArgs.RaiseExceptions
        }

    raiseExceptions <- cmdArgs.RaiseExceptions

    // Check which method should be used, i.e., verify a program, verify a transition system
    let tsList, formula =
        match cmdArgs.ExecutionMode, cmdArgs.InputFiles with
        | _, None -> raise <| HySOException "Must specify input files"
        | ExplicitSystem, Some files ->
            assert (files.Length >= 1)

            let systemPaths = files[0 .. files.Length - 2]
            let propertyPath = files[files.Length - 1]

            ModelCheckingEntryPoint.explictSystemVerification config systemPaths propertyPath

    match SecondOrderHyperLTL.SOHyperLTL.findError formula with
    | None -> ()
    | Some err -> raise <| HySOException $"Error in the formula: {err}"

    sw.Restart()
    let res = BidirectionalModelChecking.modelChecking config tsList formula
    config.Logger.LogN $"Solving Time: %i{sw.ElapsedMilliseconds}ms"


    match res with
    | SAT x, i ->
        printfn "SAT"

        if config.PrintWitness then 
            let s = (x :> FsOmegaLib.AbstractAutomaton.AbstractAutomaton<_,_>).ToHoaString string (fun (a, b) -> a + "_" + b)
            printfn $"\n{s}\n"

        config.Logger.LogN $"Iterations: %i{i}"
    | UNSAT x, i ->
        printfn "UNSAT"

        if config.PrintWitness then 
            let s = (x :> FsOmegaLib.AbstractAutomaton.AbstractAutomaton<_,_>).ToHoaString string (fun (a, b) -> a + "_" + b)
            printfn $"\n{s}\n"

        config.Logger.LogN $"Iterations: %i{i}"
    | UNKNOWN, _ -> printfn "UNKNOWN"

    swtotal.Stop()

    config.Logger.LogN
        $"Total Time %i{swtotal.ElapsedMilliseconds}ms (~=%.2f{double (swtotal.ElapsedMilliseconds) / 1000.0}s)\n\n"


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
