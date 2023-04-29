
module internal HySO.AutomataUtil

open System.Collections.Generic

open FsOmegaLib.SAT
open FsOmegaLib.AutomatonSkeleton
open FsOmegaLib.GNBA
open FsOmegaLib.NBA
open FsOmegaLib.Operations

open Util
open SolverConfiguration

/// Intersect a list of GNBAs
let constructConjunctionOfGNBAs (autList : list<GNBA<int, 'L>>) = 
    let autList = GNBA.bringToSameAPs autList

    let sumOfAccSets = 
        (0, autList)
        ||> List.mapFold (fun s x -> 
            s, s + x.NumberOfAcceptingSets
            )
        |> fst

    let initStates = 
        autList
        |> List.map (fun x -> x.InitialStates |> seq)
        |> Util.cartesianProduct
        |> set

    let queue = new Queue<_>(initStates)

    let allStates = new HashSet<_>(initStates)
    let newEdgesDict = new Dictionary<_,_>()
    let newAccSetsDict = new Dictionary<_,_>()

    while queue.Count <> 0 do 
        let n = queue.Dequeue()
        
        let edges = 
            n 
            |> List.mapi (fun i state -> autList.[i].Edges.[state] |> seq)
            |> Util.cartesianProduct
            |> Seq.choose (fun x -> 
                let guards, sucs = List.unzip x

                let combinedGuard = DNF.constructConjunction guards

                if DNF.isSat combinedGuard then  
                    if allStates.Contains sucs |> not then 
                        allStates.Add sucs |> ignore
                        queue.Enqueue sucs
                        
                    Some (combinedGuard, sucs)
                else
                    None
            )
            |> Seq.toList

        // Ensure disjoint acceptance sets
        let accSets = 
            n 
            |> List.mapi (fun i state -> autList.[i].AcceptanceSets.[state])
            |> List.mapi (fun i accSet -> 
                accSet |> Set.map (fun y -> y + sumOfAccSets.[i])
                )
            |> Set.unionMany
        
        newEdgesDict.Add(n, edges)
        newAccSetsDict.Add(n, accSets)

    {
        GNBA.Skeleton =
                {
                    AutomatonSkeleton.States = set allStates;
                    APs = autList.[0].APs
                    Edges = Util.dictToMap newEdgesDict
                };
        InitialStates = initStates;
        AcceptanceSets = Util.dictToMap newAccSetsDict;
        NumberOfAcceptingSets = autList |> List.map (fun x -> x.NumberOfAcceptingSets) |> List.sum;
    }
    |> GNBA.convertStatesToInt

