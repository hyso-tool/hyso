module HySO.BidirectionalModelChecking

open System

open FsOmegaLib.LTL
open FsOmegaLib.GNBA
open FsOmegaLib.Operations

open Util
open SolverConfiguration
open TransitionSystem
open ProductConstruction
open FirstOrderModelChecking
open SecondOrderHyperLTL
open Iteration

// Collect all set varaibles needed to evaluate this formula
let private computeNeededSetVariables (prefix : list<Quantifier<'L>>) : Set<SetVariable> = 
    let firstOrderNeed = 
        prefix
        |> List.map (fun x -> x.UsedSetVariables)
        |> Set.unionMany

    let rec addVars currentVars = 
        let a = 
            prefix
            |> List.map (fun x -> 
                currentVars
                |> Set.map (fun y -> x.SetVariablesNeededFor y)
                |> Set.unionMany
                )
            |> Set.unionMany
            |> Set.union currentVars

        if a = currentVars then 
            a
        else 
            addVars a

    addVars firstOrderNeed

let modelChecking (config : SolverConfiguration) (tslist : list<TransitionSystem<'T, 'L>>) (property : SOHyperLTL<'L>) =

    let firstOrderPrefix = 
        property.QuantifierPrefix
        |> List.choose (fun x -> 
            match x with 
            | FirstOrder (f, x, s) -> Some (f, x, s) 
            | _ -> None
            )

    let setVariableToConstructMapping = 
        property.QuantifierPrefix
        |> List.choose (fun q -> 
            match q with 
            | SecondOrder (s, y, c) -> 
                (y, (s, c)) |> Some
            | FirstOrder _ -> None
            )
        |> Map.ofList

    let fixedSetVariables, flexibleSetVariables = 
        computeNeededSetVariables property.QuantifierPrefix
        |> Set.partition (fun x -> 
            x = "all" || x.StartsWith "sys"
            )

    // This is the assignment for all setvaraibles that will never change, i.e., the system and the set of all traces
    let fixedAssignment = 
        fixedSetVariables 
        |> Set.toList
        |> List.map (fun x -> 
            let m = 
                if x = "all" then 
                    // Get the automaton that returns all traces
                    GNBA.trueAutomaton()
                else 
                    // Get the automat
                    assert (x.StartsWith "sys")
                    let tsIndex = x.[3..] |> int
                    let aut = 
                        tslist.[tsIndex]
                        |> ProductConstruction.convertSystemToGNBA tslist.[tsIndex].APs
                        |> GNBA.mapAPs (fun x -> Res x)
                        |> GNBA.convertStatesToInt
                    aut 
            x, m
            )
        |> Map.ofList

    // For all needed but non-fixed set varaibles, we create a refiner object 
    let refinerList =   
        flexibleSetVariables
        |> Set.toList 
        // Sort these in decreasing order
        |> List.sortBy (fun x -> 
            property.QuantifierPrefix
            |> List.findIndex (fun q -> 
                match q with 
                | SecondOrder (_, z, _) -> x = z
                | FirstOrder _ -> false
                )
            )
        // Map each of these varaibles to a Refiner pair 
        |> List.map (fun x -> 
            let iterator =
                match Map.tryFind x setVariableToConstructMapping with 
                | None -> 
                    failwith $"Free Variables %s{x}"
                | Some c -> 
                    // Select an apprropriate Refiner
                    match c with 
                    | (LEAST, Iteration (initDesc, stepDesc)) -> 

                        let initAut: GNBA<int,('L * String)> = 
                            FsOmegaLib.Operations.LTLConversion.convertLTLtoGNBA Util.DEBUG config.MainPath config.Ltl2tgbaPath initDesc.TransducerFormula
                            |> AutomataOperationResult.defaultWith (fun err ->
                                raise <| HySOException err.Info
                            ) 
                            |> GNBA.addAPs (initDesc.TransducerFormula |> LTL.allAtoms |> Set.toList)
                        

                        let stepAut: GNBA<int,('L * String)> = 
                            FsOmegaLib.Operations.LTLConversion.convertLTLtoGNBA Util.DEBUG config.MainPath config.Ltl2tgbaPath stepDesc.TransducerFormula
                            |> AutomataOperationResult.defaultWith (fun err ->
                                raise <| HySOException err.Info
                            ) 
                            |> GNBA.addAPs (stepDesc.TransducerFormula |> LTL.allAtoms |> Set.toList)

                        let init = {
                            IterationDesciptionAutomataon.TraceDomain = initDesc.TraceDomain
                            TransducerAutomaton = initAut
                            ProjectionTarget = initDesc.ProjectionTarget
                        }

                        let step = {
                            IterationDesciptionAutomataon.TraceDomain = stepDesc.TraceDomain
                            TransducerAutomaton = stepAut
                            ProjectionTarget = stepDesc.ProjectionTarget
                        }

                        Iteration.IterationUnderapproximation(config, fixedAssignment, x, init, step)
                    | _ -> 
                        failwith "Currently not supported."
            x, iterator
            )

    let bodyAut = 
        FsOmegaLib.Operations.LTLConversion.convertLTLtoGNBA Util.DEBUG config.MainPath config.Ltl2tgbaPath property.LTLMatrix
        |> AutomataOperationResult.defaultWith (fun err ->
            raise <| HySOException err.Info
        )  

    let negBodyAut =
        FsOmegaLib.Operations.LTLConversion.convertLTLtoGNBA Util.DEBUG config.MainPath config.Ltl2tgbaPath (LTL.Not property.LTLMatrix)
        |> AutomataOperationResult.defaultWith (fun err ->
            raise <| HySOException err.Info
        ) 

    
    let rec iterativeChecking prec precBound = 
        Util.LOGGERn $"============= Bidirectional Checking in Iteration %i{prec} ============="

        // Get the assignment by querying each iterator for its current model
        let currentAssignment = 
            refinerList
            |> Map.ofList
            |> Map.map (fun x iterator -> 
                let u = iterator.GetCurrentModel()
                Util.LOGGERn $"Current Iteration Approximation Size for %s{x}: %i{u.States.Count} "
                if iterator.ModelIsPrecise() then 
                    SecondOrderAssignment.Fixed u 
                else 
                    SecondOrderAssignment.Range (u, GNBA.trueAutomaton())
                )
            |> Util.joinMaps (Map.map (fun _ x -> Fixed x) fixedAssignment)

        // Check the first order prefix with the current model
        Util.LOGGERn $"Start First-Order Checking..."
        let r = 
            FirstOrderModelChecking.checkSatisfactionOrViolation config currentAssignment firstOrderPrefix (bodyAut, negBodyAut)

        match r with 
        | SAT -> 
            Util.LOGGERn $"============= Bidirectional Checking in Iteration %i{prec} - END ============="
            SAT, prec
        | UNSAT -> 
            Util.LOGGERn $"============= Bidirectional Checking in Iteration %i{prec} - END ============="
            UNSAT, prec
        | UNKNOWN when prec > precBound -> 
            Util.LOGGERn $"============= Bidirectional Checking in Iteration %i{prec} - END ============="
            // exeeced the bound
            UNKNOWN, prec
        | UNKNOWN -> 
            Util.LOGGERn "Start Second-Order Refinement...."
            // Need to refine the second-order assignment 

            refinerList
            |> List.iter (fun (x, iterator) -> 
                let a = iterator.Step()

                if a then 
                    // The model for x has changed, forward this to all other iterators 
                    let newRange = Range(iterator.GetCurrentModel(), GNBA.trueAutomaton())

                    refinerList
                    |> List.iter (fun (y, i) -> 
                        if y <> x then 
                            i.Update(y, newRange)
                        )
                )

            Util.LOGGERn $"============= Finished Bidirectional Checking in Iteration %i{prec} ============="
            iterativeChecking (prec + 1) precBound

    let result = iterativeChecking 0 200

    result
