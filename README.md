# GradeFourGorenstein
Macaulay2 code for experimenting with resolutions of codimension four Gorenstein ideals $`I \subset R`$. In particular, it demonstrates the "isotropic subspace" construction for producing a resolution of a codimension $`c=3`$ and type $`t=2`$ perfect ideal, whose deviation $`d`$ is equal to that of the original Gorenstein ideal. (This is an example of the $`(c-2,d,t)`$-triality phenomenon, specifically the interchange of $`c-2`$ and $`t`$.) The procedure for finding a maximal isotropic subspace is random; it is assumed that $`R`$ is a polynomial ring over a finite field and $`I`$ is homogeneous.

The code also has a "proof-of-concept" for computing a dg-algebra structure on the resolution as in Kustin-Miller. However, it is really slow if the differential $`d_2`$ is complicated.

Refer to `Demo.m2` for examples on how to use the code.
