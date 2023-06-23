# Category Theory Library in Lean 3

## Description
This is a computer-checked library of definitions, theorems, proofs and examples in the field of category theory in Lean 3.

## Installation
To run this project, you must install the following tools:
- [LEAN 3](https://leanprover-community.github.io/get_started.html)
- [`leanproject`](https://leanprover-community.github.io/leanproject.html)

When you have those installed, you can clone the repository and build the project with the following:
```bash
git clone git@gitlab.ewi.tudelft.nl:bpahrens/ct.git
cd ct
leanproject build
```
You should see it build without any problems.

## Gitlab CI/CD

 Currently there is no docker image for LEAN 4.
 This means we cannot easily set up the Gitlab Pipeline for it.
 But, there is an image for LEAN 3, therefore, we have decided to use the older version.
 
 The pipeline simply runs the command `leanproject build` on the project.
 This command will only return ok, if all code in the library is error free, ergo it is sound.

## Authors and acknowledgment

- Students:
  - Ciprian Stanciu
  - Csanád Farkas
  - Markus Orav
  - Pedro Brandão Brandao de Araujo
  - Rado Todorov
- Supervisors:
  - Benedikt Ahrens
  - Lucas Escot

## Project status
The project was developed as part of the [Research Project](https://github.com/TU-Delft-CSE/Research-Project), edition 2023 Q4, of [TU Delft](https://github.com/TU-Delft-CSE) [[1]](https://www.tudelft.nl/).
There are currently no plans beyond this course.

## License
Copyright (c) 2003 Ciprian Stanciu, Csanád Farkas, Markus Orav, Pedro Brandão Brandao de Araujo, Rado Todorov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
