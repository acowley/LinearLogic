A simple Coq development of linear logic. The library is inspired by
the paper, J. Power and C. Webster, **"Working with linear logic in
coq,"** in _The 12th International Conference on Theorem Proving in
Higher Order Logics_, 1999.

This particular devlopment is based more immediately on that used in
A. Cowley and C.J. Taylor, **"Stream-oriented robotics programming:
The design of roshask,"** in _Proceedings of the IEEE/RJS
International Conference on Intelligent Robots and Systems (IROS)_,
2011. [pdf](http://www.seas.upenn.edu/~acowley/papers/TowardsLinear.pdf)

Tested with [the Rocq Prover](https://rocq-prover.org/) 9.0.

An example command to build the documentation,

    rocq doc --no-lib-name -d doc *.v --utf8 --no-index

(this requires that the directory `doc` exists).
