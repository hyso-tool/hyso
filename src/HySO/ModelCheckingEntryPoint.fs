module HySO.ModelCheckingEntryPoint

open System.IO

open Util
open SolverConfiguration

let explictSystemVerification (config : SolverConfiguration) systemPaths propPath  = 
    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    let propertyContent =   
        try 
            File.ReadAllText propPath
        with 
            | _ -> 
                raise <| AnalysisException $"Could not open/read file %s{propPath}"
                
    let tscontent = 
        systemPaths
        |> List.map (fun x -> 
                try 
                    File.ReadAllText  x
                with 
                    | _ -> 
                        raise <| AnalysisException $"Could not open/read file %s{x}"
            )

    Util.LOGGERn $"Read Input in: %i{sw.ElapsedMilliseconds}ms"

    sw.Restart()

    let property =
        match SecondOrderHyperLTL.Parser.parseSecondOrderHyperLTL Util.ParserUtil.escapedStringParser propertyContent with 
            | Result.Ok x ->
                x
            | Result.Error err -> 
                raise <| AnalysisException $"The formula could not be parsed: %s{err}"
                
       
    let tslist = 
        tscontent
        |> List.map (fun x -> 
            match TransitionSystem.Parser.parseTS x with 
                | Result.Ok y -> y 
                | Result.Error err -> 
                    raise <| AnalysisException $"The system could not be parsed: %s{err}"
            )

    Util.LOGGERn  $"Parsed Input in: %i{sw.ElapsedMilliseconds}ms"
    
    tslist
    |> List.iteri (fun i x ->
        if x.IsConsistent() |> not then
            raise <| AnalysisException $"The %i{i}th transition system is inconsistent"
        )

    sw.Restart()
    let res = BidirectionalModelChecking.modelChecking config tslist property
    Util.LOGGERn $"Solving Time: %i{sw.ElapsedMilliseconds}ms"
    
    res
