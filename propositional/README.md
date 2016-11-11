propositional theorem prover using the tableaux method
implemented in OCaml

once you've loaded the file in ocaml, you can try stuff like

    let p = Impl(Atom "a",Atom "a");;
    itt p;;

to declare a proposition "A implies A" and generate a PDF of the proof done in
LaTeX. this assumes you have pdflatex installed on your computer. if you just
want a yes/no answer then you can use

       	solve p;;

instead.
