module HySO.LassoPath 

type LassoPath<'L> = 
    {
        Prefix : list<'L>
        Loop : list<'L>
    }

    member this.Map f = 
        {
            Prefix = this.Prefix |> List.map f
            Loop = this.Loop |> List.map f
        }

    member this.GetElement (i : int) = 
        if i < this.Prefix.Length then 
            this.Prefix.[i]
        else 
            let lassoIndex = (i - this.Prefix.Length) % this.Loop.Length
            this.Loop.[lassoIndex]

    member this.GetPrefix (i : int) =   
        [0..i]
        |> List.map (fun j -> this.GetElement j)