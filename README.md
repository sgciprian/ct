# Category Theory Library in Lean 3

## Description
The aim of this project is to make a computer checked library of definitions, theorems, proofs and examples in the field of Category Theory.
The language used is Lean 3, more technical details can be found later in this document.

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

## Support
Tell people where they can go to for help. It can be any combination of an issue tracker, a chat room, an email address, etc.

## Roadmap
If you have ideas for releases in the future, it is a good idea to list them in the README.

## Contributing
State if you are open to contributions and what your requirements are for accepting them.

For people who want to make changes to your project, it's helpful to have some documentation on how to get started. Perhaps there is a script that they should run or some environment variables that they need to set. Make these steps explicit. These instructions could also be useful to your future self.

You can also document commands to lint the code or run tests. These steps help to ensure high code quality and reduce the likelihood that the changes inadvertently break something. Having instructions for running tests is especially helpful if it requires external setup, such as starting a Selenium server for testing in a browser.

### Gitlab CI/CD

 Currently there is no docker image for LEAN 4.
 This means we cannot easily set up the Gitlab Pipeline for it.
 But, there is an image for LEAN 3, therefore, we have decided to use the older version.
 
 The pipeline simply runs the command `leanproject build` on the project.
 This command will only return ok, if all code in the library is error free, ergo it is sound.

## Authors and acknowledgment

- Students:
  - Ciprian Stanciu
  - Csanád Farkas
  - Markus
  - Pedro Brandão Brandao de Araujo
  - Rado Todorov
- Supervisors:
  - Benedikt Ahrens
  - Lucas Escot

## License
!! what license do we have? !!

## Project status
The project is currently developed as a Research Project for a University course of the same name, given by TU Delft.
There are currently no plans beyond this course.
