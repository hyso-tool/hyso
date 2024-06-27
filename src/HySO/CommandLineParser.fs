module HySO.CommandLineParser

open System

type ExecutionMode = 
    | ExplictSystem of list<String> * string
    | INVALID


type CommandLineArguments = 
    {
        ExecMode : ExecutionMode
        LogPrintouts : bool
        RaiseExceptions : bool
    }

    static member Default = 
        {
            ExecMode = INVALID
            LogPrintouts = false
            RaiseExceptions = false
        }

let rec private splitByPredicate (f : 'T -> bool) (xs : list<'T>) = 
    match xs with 
        | [] -> [], []
        | x::xs -> 
            if f x then 
                [], x::xs 
            else 
                let r1, r2 = splitByPredicate f xs 
                x::r1, r2

let parseCommandLineArguments (args : list<String>) =
    let rec parseArgumentsRec (args : list<String>) (opt : CommandLineArguments) = 

        match args with 
            | [] -> Result.Ok opt
            | x::xs -> 
                match x with 
                    | "-i" -> 
                        let args, ys = splitByPredicate (fun (x : string) -> x.[0] = '-') xs
            
                        if List.length args < 2 then 
                            Result.Error "Option -i must be followed by at least two arguments"
                        else 
                            let propertyFile = args[args.Length - 1]
                            let systemFiles = args[0..args.Length - 2]
                            parseArgumentsRec ys {opt with ExecMode = ExplictSystem(systemFiles, propertyFile)}  
                    | "--log" -> 
                        parseArgumentsRec xs {opt with LogPrintouts = true} 
                    | _ -> Result.Error ("Option " + x + " is not supported" )
        
    parseArgumentsRec args CommandLineArguments.Default