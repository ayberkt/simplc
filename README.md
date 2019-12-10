# `simplc` ![build status](https://gitlab.com/ayberkt/simplc/badges/master/pipeline.svg)

`simpl` is a tiny security-typed imperative programming language close to the
one from Sabelfeld and Myers (2003) defined in `Imp.agda`. `simplc` is a
compiler from `simpl` to a little stack-based machine defined in `Machine.agda`.

The fact that all well-typed `simpl` programs have the _noninterference_
property is formalized in `Noninterference.agda`. In addition to this, we have
formulated a natural notion of noninterference for the machine and have
formalized the proof that the compilation of every well-typed `simpl` program
results in a noninterferent machine program; this theorem goes under the name
`main-theorem` and lives in `Compiler.agda`

## References

- Sabelfeld, A., & Myers, A. C. (2003). Language-based information-flow security.
  IEEE Journal on selected areas in communications, 21(1), 5-19.
  
# Credits

Authors are Ayberk Tosun (`@ayberkt`) and Alexander Fuhs (`@haskell-user`).

This development was carried out as the final project for the language-based
security course (`TDA602`) taught by Andrei Sabelfeld at Chalmers University of
Technology.

We are grateful to _Marco Vassena_ and _Andrei Sabelfeld_ for suggestions and
guidance.

[1]: https://gitlab.com/ayberkt/simplc/badges/master/pipeline.svg
