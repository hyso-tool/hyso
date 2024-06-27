module HySO.Iteration

open System

open FsOmegaLib.AutomatonSkeleton
open FsOmegaLib.GNBA
open FsOmegaLib.Operations

open Util
open Configuration
open SecondOrderHyperLTL
open ProductConstruction
open FirstOrderModelChecking


type IterationDesciptionAutomataon<'T, 'L when 'L: comparison and 'T: comparison>  = 
    {
        TraceDomain : Map<TraceVariable, SetVariable>;
        TransducerAutomaton : GNBA<'T, 'L * TraceVariable>;
        ProjectionTarget : TraceVariable
    }

type private IntermediateFunctionLabel<'L> = 
    // Takes the same role as an Arg
    | IntArg of 'L * TraceVariable 
    // Record the intermediate output of some automaton used in the iteration
    | IntRes of 'L * string


let computeProjectionAutomaton (soAssignment : Map<SetVariable, GNBA<int, FunctionLabel<'L>>>) (desc: IterationDesciptionAutomataon<int
, 'L>) (includeInRange : 'L -> bool) : GNBA<int, FunctionLabel<'L>> = 

    let distinctTransducerIndices = 
        desc.TransducerAutomaton.APs
        |> List.map snd
        // We only consider those trace varaibles that are resolved on an automataon and thus not part of the function arguments 
        |> List.filter (fun pi -> Map.containsKey pi desc.TraceDomain)
        |> List.distinct

    // For each index we generte a unqiue name. This is used to later compose with the transducer automaton in the correct positions
    let indexToNameMap = 
        distinctTransducerIndices
        |> List.mapi (fun i l -> l, "_index" + string(i))
        |> Map.ofList

    // We genarte one GNBA copy for each indicw we need. The result of each such function GNBA is mapped to the proposition 
    let modelList = 
        distinctTransducerIndices
        |> List.map (fun l -> 
            assert (Map.containsKey l desc.TraceDomain) 
            soAssignment.[desc.TraceDomain.[l]]
            |> GNBA.mapAPs (fun y -> 
                match y with
                | Arg (y, ind) -> IntArg (y, ind)
                | Res y -> IntRes (y, indexToNameMap.[l])
                )
            )

    let transducerAutomaton = 
        desc.TransducerAutomaton
        |> GNBA.mapAPs (fun (x, l) -> 
            if Map.containsKey l desc.TraceDomain then 
                // This variable is reolved on a given automataon. Rename the AP to match the output of that automataon 
                IntRes (x, indexToNameMap.[l])
            else 
                // This trace is not resolved on a given set and thus part of the function
                IntArg(x, l)
            )

    let auts = transducerAutomaton::modelList

    let combinedAps = 
        auts
        |> List.map (fun x -> x.APs)
        |> List.concat 
        |> List.distinct

    let newAPs = 
        combinedAps
        |> List.filter (fun x -> 
            match x with 
            | IntArg _ -> true
            | IntRes (x, i) -> 
                // Only keep those result APs that match the target && are in the fixed APs that we care about
                i = indexToNameMap.[desc.ProjectionTarget] && (includeInRange x)
                 
        )

    let resGNBA = 
        auts 
        |> AutomataUtil.constructConjunctionOfGNBAs
        |> GNBA.projectToTargetAPs newAPs

    {
        GNBA.Skeleton = 
            {
                AutomatonSkeleton.States = resGNBA.States
                APs = 
                    resGNBA.APs 
                    |> List.map (fun x -> 
                        match x with 
                        | IntArg (y, index) -> Arg (y, index)
                        | IntRes (y, _) -> Res y);
                Edges = 
                    resGNBA.Edges
            }
        InitialStates = resGNBA.InitialStates
        NumberOfAcceptingSets = resGNBA.NumberOfAcceptingSets
        AcceptanceSets = resGNBA.AcceptanceSets
    }
    |> GNBA.convertStatesToInt



// A Refiner that maintains an underapprximation by iterating a transducer
type IterationUnderapproximation<'L when 'L: comparison> (config: Configuration, fixedAssignments : Map<SetVariable, GNBA<int, FunctionLabel<'L>>>, name : SetVariable, init : IterationDesciptionAutomataon<int, 'L>, step : IterationDesciptionAutomataon<int, 'L>) =

    let mutable env: Map<SetVariable,SecondOrderAssignment<'L>>  = Map.empty
    let mutable envHasChanged = true
    let mutable hasConverged = false

    // We initilize the current model with the emptyset
    let mutable currentModel = GNBA.falseAutomaton()

    let relevantSetVariables = 
        (
            init.TransducerAutomaton.APs 
            |> List.map snd 
            |> List.choose (fun x -> Map.tryFind x init.TraceDomain)
        )
        @
        (
            step.TransducerAutomaton.APs 
            |> List.map snd 
            |> List.choose (fun x -> Map.tryFind x step.TraceDomain)
        )
        |> List.filter (fun x -> x <> name)
        |> List.distinct

    let initModel = computeProjectionAutomaton fixedAssignments init (fun _ -> true)


    do 
        // All variable sets are initilized to the range of all sets
        relevantSetVariables
        |> List.iter (fun x -> 
            env <- Map.add x (Range (GNBA.falseAutomaton(), GNBA.trueAutomaton())) env 
        )

        // We fix the model for all fixed sets
        fixedAssignments 
        |> Map.iter (fun k v -> 
            env <- 
                Map.add k (Fixed v) env
            )

        // We only support initial formulas that do not refer to other second-order variables
        init.TraceDomain.Values
        |> Seq.iter (fun x -> 
            assert (fixedAssignments.ContainsKey x)
            )

        // We compute the initial approximation of this model by iterting the initial condition
        currentModel <- initModel


    member this.GetCurrentModel () : GNBA<int,FunctionLabel<'L>> = 
        currentModel 
    
    member this.ModelIsPrecise () = 
        hasConverged && not envHasChanged

    member this.HasConverged () = 
        hasConverged && not envHasChanged

    member this.Step () = 
        if hasConverged && not envHasChanged then 
            // Nothing to do. The model did not change
            false
        else 
            // As we are computing an under-approximation, we are only interested in the under-approximation of the other models
            // For the current name, we simply take the current model
            let under =
                relevantSetVariables
                |> List.map (fun x -> 
                    x, env.[x].Under
                )
                |> Map.ofList
                |> Map.add name currentModel


            let iterRes = computeProjectionAutomaton under step (fun _ -> true)
            
            let union = 
                FsOmegaLib.Operations.AutomataOperations.unionToGNBA config.RaiseExceptions config.SolverConfig.MainPath config.SolverConfig.AutfiltPath Effort.HIGH currentModel iterRes
                |> AutomataOperationResult.defaultWith (fun err ->
                        raise <| HySOException err.Info
                    )  

            // We check if we have converged to the iteration fixpoint
            let hasReachedFixpoint = 
                FsOmegaLib.Operations.AutomataChecks.isEquivalent config.RaiseExceptions config.SolverConfig.MainPath config.SolverConfig.AutfiltPath union currentModel
                |> AutomataOperationResult.defaultWith (fun err ->
                    raise <| HySOException err.Info
                )  

            // We have done one iteration with the new env, so we can set this to false
            envHasChanged <- false
            
            if hasReachedFixpoint then 
                // The last iteration did not change the model
                config.Logger.LogN "#############################"
                config.Logger.LogN "## Iteration has converged ##"
                config.Logger.LogN "#############################"
                hasConverged <- true
                false
            else 
                currentModel <- union
                hasConverged <- false
                true

    member this.Update (x, sol) = 
        if List.contains x relevantSetVariables && x <> name then 
            config.Logger.LogN $"Set varaible %s{x} has been changed. Restart the computation for %s{name}."
            // We update the env and set the flag that this has been updated
            env <- Map.add x sol env
            envHasChanged <- true
            //hasConverged <- false

            // Some of the other models have changed so we need to restart with the initial model
            //currentModel <- initModel


