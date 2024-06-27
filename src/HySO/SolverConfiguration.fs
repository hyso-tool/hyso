module HySO.SolverConfiguration 

open System.IO

open Util 
open Json

type SolverConfiguration = 
    {
        MainPath : string;
        AutfiltPath : string
        Ltl2tgbaPath : string
    }

let private parseSolverConfig (s : string) =
    match Json.Parser.parseJsonString s with 
    | Result.Error err -> raise <| HySOException $"Could not parse config file: %s{err}"
    | Result.Ok x -> 
        {
            MainPath = "./"
            AutfiltPath =
                (Json.tryLookup "autfilt" x)
                |> Option.defaultWith (fun _ -> raise <| HySOException "No field 'autfilt' found")
                |> Json.tryGetString
                |> Option.defaultWith (fun _ -> raise <| HySOException "Field 'autfilt' must contain a string")
            Ltl2tgbaPath = 
                (Json.tryLookup "ltl2tgba" x)
                |> Option.defaultWith (fun _ -> raise <| HySOException "No field 'ltl2tgba' found")
                |> Json.tryGetString
                |> Option.defaultWith (fun _ -> raise <| HySOException "Field 'ltl2tgba' must contain a string")
        }

let getSolverConfig() = 
    // By convention the paths.json file is located in the same directory as the executable
    let configPath = 
        System.IO.Path.Join [|System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location); "paths.json"|]
                     
    // Check if the path to the config file is valid, i.e., the file exists
    if System.IO.FileInfo(configPath).Exists |> not then 
        raise <| HySOException "The paths.json file does not exist in the same directory as the executable"            
    
    // Parse the config file
    let configContent = 
        try
            File.ReadAllText configPath
        with 
            | _ -> 
                raise <| HySOException "Could not open paths.json file"

    let solverConfig = parseSolverConfig configContent

    if System.IO.FileInfo(solverConfig.AutfiltPath).Exists |> not then 
        raise <| HySOException "The path to the spot's autfilt is incorrect"

    if System.IO.FileInfo(solverConfig.Ltl2tgbaPath).Exists |> not then 
        raise <| HySOException "The path to the spot's ltl2tgba is incorrect"
    
    solverConfig