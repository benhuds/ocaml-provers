(requires ocaml)

first-order logic theorem prover by resolution.

once you've loaded the file in ocaml, you can use `run` to prove a formula in
FOL.

e.g.

    let d = FExists("y" , FImp(FRel("D" , 1 , [Var "y"]) , FForall("x" , FRel("D" , 1 , [Var "x"]))));;
    run d;;

where `d` is the [drinker's paradox](https://en.wikipedia.org/wiki/Drinker_paradox):
"there exists someone in the bar such that whenever they drink, everyone in the bar drinks."
