module HySO.SecondOrderHyperLTL

open FsOmegaLib.LTL

type TraceVariable = string 

type SetVariable = string 

type FixpointOperation = 
    | LEAST 
    | GREATEST

type IterationDescription<'L when 'L: comparison>  = 
    {
        TraceDomain : Map<TraceVariable, SetVariable>;
        TransducerFormula : LTL<'L * TraceVariable>;
        ProjectionTarget : TraceVariable
    }

    member this.UsedVariables = 
        this.TraceDomain.Values |> set


type FirstOrderQuantifierType = 
    | FORALL
    | EXISTS
    
type SecondOrderConstruction<'L when 'L: comparison> = 
    | Iteration of init : IterationDescription<'L> * step : IterationDescription<'L>

    member this.UsedSetVariables = 
        match this with 
        | Iteration (init, step) -> Set.union init.UsedVariables step.UsedVariables


and Quantifier<'L when 'L: comparison> = 
    | FirstOrder of FirstOrderQuantifierType * TraceVariable * SetVariable
    | SecondOrder of FixpointOperation * SetVariable * SecondOrderConstruction<'L>

    member this.SetVariablesNeededFor (x : SetVariable) =
        match this with 
        | SecondOrder(_, y, c) when y = x -> 
            c.UsedSetVariables
        | _ -> Set.empty
        

    member this.UsedSetVariables = 
        match this with 
        | FirstOrder (_, _, x) -> Set.singleton x
        | SecondOrder _ -> Set.empty

and SOHyperLTL<'L when 'L: comparison> = 
    {
        QuantifierPrefix : list<Quantifier<'L>>
        LTLMatrix : LTL<'L * TraceVariable>
    }

module Parser =
    open FParsec

    let private traceVarParser = 
        many1Chars (letter <|> digit)

    let private setVarParser = 
        many1Chars (letter <|> digit)


    let private prefixParser indexedAtomParser = 
        let forallParser = 
            pipe2 
                (skipString "forall" >>. spaces >>. traceVarParser)
                (spaces >>. skipChar ':' >>. spaces >>. setVarParser .>> spaces .>> skipChar '.')
                (fun x y -> (FORALL, x, y) |> FirstOrder)

        let existsParser = 
            pipe2 
                (skipString "exists" >>. spaces >>. traceVarParser)
                (spaces >>. skipChar ':' >>. spaces >>. setVarParser .>> spaces .>> skipChar '.')
                (fun x y -> (EXISTS, x, y) |> FirstOrder)

        let secondOrderConstructionParser indexedAtomParser = 
            let iterationParser (indexedAtomParser : Parser<'T * TraceVariable, unit>) = 
                let asignmentParser = 
                    skipChar '[' >>. spaces >>. sepBy ((traceVarParser .>> spaces .>> skipChar ':') .>>. (spaces >>. setVarParser .>> spaces)) (skipChar ',' .>> spaces) .>> spaces .>> skipChar ']'

                Util.ParserUtil.pipe6
                    (skipString "iter" >>. spaces >>. skipChar '(' >>. spaces >>. asignmentParser .>> spaces .>> skipChar ',')
                    (spaces >>. FsOmegaLib.LTL.Parser.ltlParser indexedAtomParser .>> spaces .>> skipChar ',')
                    (spaces >>. traceVarParser .>> spaces .>> skipChar ',')
                    (spaces >>. asignmentParser .>> spaces .>> skipChar ',')
                    (spaces >>. FsOmegaLib.LTL.Parser.ltlParser indexedAtomParser .>> spaces .>> skipChar ',')
                    (spaces >>. traceVarParser .>> spaces .>> skipChar ')')
                    (fun a b c d e f ->
                        let init = 
                            {
                                IterationDescription.TraceDomain = Map.ofList a
                                TransducerFormula = b
                                ProjectionTarget = c
                            }

                        let step = 
                            {
                                IterationDescription.TraceDomain = Map.ofList d;
                                TransducerFormula = e;
                                ProjectionTarget = f;
                            }
                        
                        Iteration(init=init, step=step)
                    )


            choice [
                iterationParser indexedAtomParser
            ]

        let secondOrderMu indexedAtomParser = 
            pipe2 
                (skipString "mu" >>. spaces >>. setVarParser)
                (spaces >>. skipChar ':' >>. spaces >>. secondOrderConstructionParser indexedAtomParser  .>> spaces .>> skipChar '.')
                (fun x f -> SecondOrder(LEAST, x, f))

        many1 ((forallParser <|> existsParser <|> secondOrderMu indexedAtomParser) .>> spaces)


    let private secondOrderHyperLTLParser (atomParser : Parser<'T, unit>) = 
        let ap : Parser<'T * string, unit>= 
            atomParser .>> pchar '_' .>>. (many1Chars letter)

        pipe2 
            (spaces >>. prefixParser ap)
            (FsOmegaLib.LTL.Parser.ltlParser ap)
            (fun x y -> {SOHyperLTL.QuantifierPrefix = x; LTLMatrix = y})
    
    let parseSecondOrderHyperLTL (atomParser : Parser<'T, unit>) s =    
        let full = secondOrderHyperLTLParser atomParser .>> spaces .>> eof
        let res = run full s
        match res with
        | Success (res, _, _) -> Result.Ok res
        | Failure (err, _, _) -> Result.Error err
    