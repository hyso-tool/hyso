module HySO.SolverConfiguration 

open System
open System.IO

open FsOmegaLib.JSON

open Util 

type SolverConfiguration = 
    {
        MainPath : String;
        AutfiltPath : String
        Ltl2tgbaPath : String
    }

let private parseConfigFile (s : string) =
    match FsOmegaLib.JSON.Parser.parseJsonString s with 
    | Result.Error err -> raise <| AnalysisException $"Could not parse config file: %s{err}"
    | Result.Ok x -> 
        {
            MainPath = "./"
            AutfiltPath =
                (JSON.tryLookup "autfilt" x)
                |> Option.bind (fun x -> JSON.tryGetString x)
                |> Option.defaultWith (fun _ -> raise <| AnalysisException "Must specify path to autfilt")
            Ltl2tgbaPath = 
                (JSON.tryLookup "ltl2tgba" x)
                |> Option.bind (fun x -> JSON.tryGetString x)
                |> Option.defaultWith (fun _ -> raise <| AnalysisException "Must specify path to ltl2tgba")
        }

let getConfig() = 
    // By convention the paths.json file is located in the same directory as the executable
    let configPath = 
        System.IO.Path.Join [|System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location); "paths.json"|]
                     
    // Check if the path to the config file is valid, i.e., the file exists
    if System.IO.FileInfo(configPath).Exists |> not then 
        raise <| AnalysisException "The paths.json file does not exist in the same directory as the executable"            
    
    // Parse the config file
    let configContent = 
        try
            File.ReadAllText configPath
        with 
            | _ -> 
                raise <| AnalysisException "Could not open paths.json file"

    let solverConfig = parseConfigFile configContent

    if System.IO.FileInfo(solverConfig.AutfiltPath).Exists |> not then 
        raise <| AnalysisException "The path to the spot's autfilt is incorrect"

    if System.IO.FileInfo(solverConfig.Ltl2tgbaPath).Exists |> not then 
        raise <| AnalysisException "The path to the spot's ltl2tgba is incorrect"
    
    solverConfig