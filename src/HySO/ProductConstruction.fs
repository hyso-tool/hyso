module HySO.ProductConstruction

open System.Collections.Generic

open TransitionSystem
open FsOmegaLib.SAT
open FsOmegaLib.AutomatonSkeleton
open FsOmegaLib.GNBA

open SecondOrderHyperLTL

type FunctionLabel<'L> = 
    | Arg of 'L * TraceVariable 
    | Res of 'L

/// Given an automaton, a list of system and a list of indices construct the product of the automaton and the transition systems
let constructExistentialProductWithFunction (aut : GNBA<int, 'L * TraceVariable>) (func : GNBA<int, FunctionLabel<'L>>) (index : TraceVariable) (project : bool) = 
    // The results of the function automaton is resolved on the ``index`` trace
    let transformedFunc = 
        func 
        |> GNBA.mapAPs (fun x -> 
            match x with
            | Arg (y, l) -> (y, l)
            | Res y -> y, index
            )

    let combinedAps = 
        aut.APs @ transformedFunc.APs 
        |> List.distinct

    // Compute the APs that will be used in the final automaton.
    // These are all propositions except those indexed by ``position``
    let newAPs = 
        combinedAps
        |> List.filter (fun (_, i) -> i <> index)

    let resGNBA = 
        [aut; transformedFunc]
        |> AutomataUtil.constructConjunctionOfGNBAs
        
    if project then 
        GNBA.projectToTargetAPs newAPs resGNBA 
    else 
        resGNBA


/// Given a system and a matching list of relevant propositions, construct an NBA that accepts the traces of the system system (projected on the relevant propositions)
let convertSystemToGNBA (interestingAps : list<'L>) (ts : TransitionSystem<'T, 'L>) = 
    // Assert that all interesting aps are also aps in the transition system
    assert(
        ts.APs
        |> List.forall (fun x -> List.contains x interestingAps))

    let apMapping = 
        interestingAps
        |> List.mapi (fun i a -> i, ts.APs |> List.findIndex ((=) a))
        |> Map.ofList

    let queue = new Queue<_>(ts.InitialStates)
    let edgesDict = new Dictionary<_,_>()
    let allStates = new HashSet<_>(ts.InitialStates)

    while queue.Count <> 0 do 
        let tstate = queue.Dequeue()

        let sucs, apEval = ts.Step.[tstate]

        // This is simply a conjunction of literals that hold in the given state and are put on all outgoing transitions
        let guardDNF : DNF<int> = 
            [0..interestingAps.Length - 1]
            |> List.map (fun i -> 
                let b = apEval.[apMapping.[i]]
                if b then Literal.PL i else Literal.NL i
                )
            |> List.singleton 

        let outgoingEdges = 
            sucs
            |> Seq.toList
            |> List.map (fun x -> guardDNF, x)

        edgesDict.Add(tstate, outgoingEdges)
        
        for tstate' in sucs do 
            if allStates.Contains tstate' |> not then 
                allStates.Add tstate' |> ignore 
                queue.Enqueue tstate'


    {
        GNBA.Skeleton = 
            {
                AutomatonSkeleton.States = allStates |> set;
                Edges = Util.dictToMap edgesDict
                APs = interestingAps
            };
        InitialStates = ts.InitialStates |> set
        NumberOfAcceptingSets = 0
        AcceptanceSets = 
            allStates
            |> Seq.map (fun x -> x, Set.empty)
            |> Map.ofSeq
    }