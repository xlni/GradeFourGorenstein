# GradeFourGorenstein
Macaulay2 code for experimenting with resolutions of codimension four Gorenstein ideals $`I \subset R`$. In particular, it demonstrates the "isotropic subspace" construction for producing a resolution of a codimension three perfect ideal, whose deviation is equal to that of the original Gorenstein ideal. The procedure for finding a maximal isotropic subspace is random; it is assumed that $`R`$ is a polynomial ring over a finite field and $`I`$ is homogeneous.

The code also has a "proof-of-concept" for computing a dg-algebra structure on the resolution as in Kustin-Miller. However, it is prohibitively slow.

Refer to `Demo.m2` for examples on how to use the code.