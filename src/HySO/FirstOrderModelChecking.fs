module HySO.FirstOrderModelChecking

open System

open FsOmegaLib.SAT
open FsOmegaLib.GNBA
open FsOmegaLib.Operations

open Util
open SolverConfiguration
open LassoPath
open ProductConstruction
open SecondOrderHyperLTL


type SecondOrderAssignment<'L when 'L: comparison> = 
    // Gives an under and an over approximation
    | Range of GNBA<int, FunctionLabel<'L>> * GNBA<int, FunctionLabel<'L>> 
    // Gives the fixed system 
    | Fixed of GNBA<int, FunctionLabel<'L>>

    member this.Under = 
        match this with
        | Range (a, _) -> a
        | Fixed a -> a

    member this.Over = 
        match this with
        | Range (_, b) -> b
        | Fixed a -> a

type FirstOrderCheckingResult = 
    | FO_SAT 
    | FO_UNSAT 

let rec private outsideInModelChecking (config : SolverConfiguration) (soAssignment : Map<SetVariable, SecondOrderAssignment<'L>>) (quantifierPrefix : list<FirstOrderQuantifierType * TraceVariable * SetVariable>) (aut : GNBA<int, 'L * String>, isNegated : bool) = 
    
    if quantifierPrefix.IsEmpty then 
        assert (aut.APs.Length = 0)

        Util.LOGGERn $"Checking for emptiness..."

        let isEmpty = 
            FsOmegaLib.Operations.AutomataChecks.isEmpty Util.DEBUG config.MainPath config.AutfiltPath aut
            |> AutomataOperationResult.defaultWith (fun err ->
                raise <| HySOException err.Info
            ) 

        if (isEmpty && not isNegated) || (not isEmpty && isNegated) then 
            // The property does not hold
            FO_UNSAT
        else 
            FO_SAT
    else
        let lastQunatifier = List.last quantifierPrefix
        let remainingPrefix = quantifierPrefix[..quantifierPrefix.Length - 2]

        match lastQunatifier with 
        | (EXISTS, pi, x)  -> 
            Util.LOGGERn $"Start checking of exists %s{pi} : %s{x}..."
            // Make sure that the automaton is positive
            let positiveAut = 
                if isNegated then 
                    Util.LOGGERn $"Start automaton complementation..."
                    FsOmegaLib.Operations.AutomataOperations.complementToGNBA Util.DEBUG config.MainPath config.AutfiltPath Effort.HIGH aut
                    |> AutomataOperationResult.defaultWith (fun err ->
                        raise <| HySOException err.Info
                    ) 
                else 
                    aut

            // Construct the product with the under-approximation
            let nextAut = ProductConstruction.constructExistentialProductWithFunction positiveAut soAssignment.[x].Under pi true
            
            outsideInModelChecking config soAssignment remainingPrefix (nextAut, false)
            

        | (FORALL, pi, x) -> 
            Util.LOGGERn $"Start checking of forall %s{pi} : %s{x}..."
            // Make sure the automaton is negated
            let negativeAut = 
                if not isNegated then 
                    Util.LOGGERn $"Start automaton complementation..."
                    FsOmegaLib.Operations.AutomataOperations.complementToGNBA Util.DEBUG config.MainPath config.AutfiltPath Effort.HIGH aut
                    |> AutomataOperationResult.defaultWith (fun err ->
                        raise <| HySOException err.Info
                    ) 
                else 
                    aut

                // Construct the product with the overapproximation
            let nextAut =  ProductConstruction.constructExistentialProductWithFunction negativeAut soAssignment.[x].Over pi true

            outsideInModelChecking config soAssignment remainingPrefix (nextAut, true)
            

type VerificationResult = 
    | SAT 
    | UNSAT 
    | UNKNOWN

let checkSatisfactionOrViolation (config : SolverConfiguration) (soAssignment : Map<SetVariable, SecondOrderAssignment<'L>>) (quantifierPrefix : list<FirstOrderQuantifierType * TraceVariable * SetVariable>) (aut : GNBA<int, 'L * String>, negAut : GNBA<int, 'L * String>) = 

    // We first check if the formula holds 
    Util.LOGGERn $"---------- SAT Check ----------"
    let posRes = 
        match List.last quantifierPrefix with 
        | (EXISTS, _, _) -> 
            outsideInModelChecking config soAssignment quantifierPrefix (aut, false)
        | (FORALL, _, _) -> 
            outsideInModelChecking config soAssignment quantifierPrefix (negAut, true)

    Util.LOGGERn $"---------- SAT Check - END ----------"

    match posRes with 
    | FO_SAT -> 
        // The formula holds!
        SAT
    | FO_UNSAT -> 
        // UNSAT, we check if we get a decisive result by checking the negation
        let flippedPrefix = 
            quantifierPrefix
            |> List.map (fun q -> 
                match q with 
                | (FORALL, x, y) -> (EXISTS, x, y)
                | (EXISTS, x, y) -> (FORALL, x, y) 
            )

        Util.LOGGERn $"---------- UNSAT Check ----------"
        // We check the negated formula, i.e., flip the prefix and use the negated body
        let negRes = 
            match List.last flippedPrefix with 
            | (EXISTS, _, _) -> 
                outsideInModelChecking config soAssignment flippedPrefix (negAut, false)
            | (FORALL, _, _) -> 
                outsideInModelChecking config soAssignment flippedPrefix (aut, true)
        Util.LOGGERn $"---------- UNSAT Check - END ----------"
        match negRes with 
        | FO_SAT -> 
            // The negation holds, so the orginal formula does not
            UNSAT
        | FO_UNSAT ->
            // No statement is possible
            UNKNOWN