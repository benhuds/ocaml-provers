(requires ocaml, pdflatex if you want to generate PDF output of your tableaux
proof)

propositional theorem prover using the tableaux method.

once you've loaded the file in ocaml, you can try stuff like

```ocaml
let p = Impl(Atom "a",Atom "a");;
itt p;;
```

to declare a proposition "A implies A" and generate a PDF of the proof done in
LaTeX. If you don't have pdflatex installed or if you just want a yes/no answer
then you can use

```ocaml
solve p;;
```

instead. The tableaux method is syntax-directed so the implementation of the
basic `solve` function is pretty straightforward. It gets more interesting when
you want to print the proof tree in LaTeX. 
