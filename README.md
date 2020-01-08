# Short presentations of alternating and symmetric groups
This repository is a supplement to my honours dissertation on short presentations of alternating and symmetric groups. The dissertation is submitted in partial fulfillment of the requirements for the degree of BSc(Hons) in Mathematics, The University of Auckland, 2019. There are also some additional presentations which have been added to this repository after the dissertation was submitted.

## Supervisor
[Eamonn O'Brien](https://www.math.auckland.ac.nz/~obrien/), The University of Auckland.

## Central paper
\[GKKL\] Guralnick, R. M., Kantor, W. M., Kassabov, M., Lubotzky, A. [Presentations of finite simple groups: a computational approach](http://dx.doi.org/10.4171/JEMS/257). J. Eur. Math. Soc. 13, 391–458 (2011).

## Description
The dissertation explicitly defines 3-generator 7-relator presentations of alternating and symmetric groups, and corresponding generators in the standard copies of these groups. [Magma](http://magma.maths.usyd.edu.au/magma/) functions are supplied in `altsym.m` which construct the relators as elements of an `SLPGroup` (short-line programs), as well as others which return the corresponding generators as permutations. Presentations of other groups appearing in \[GKKL\] have been included in `sl.m`, including presentations for the special linear groups over finite fields, parts of this code are due to Eamonn O'Brien.
