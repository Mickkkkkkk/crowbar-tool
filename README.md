# Crowbar 

**Crowbar** is a symbolic execution engine for [**ABS**](https://abs-models.org), based on [**BPL**](https://doi.org/10.1007/978-3-030-29026-9_22).
Crowbar aims to provide a possibility to prototype novel deductive verification techniques for 
functional correctness of Active Objects. 

Documentation for users and developers can be found in the [wiki](https://github.com/Edkamb/crowbar-tool/wiki).

## Installation
Crowbar requires Java >= 1.11 and an SMT-Solver to run. 
On an Ubuntu/Linux machine, run
```
sudo apt-get install z3
mkdir crowbar
cd crowbar
git clone https://github.com/Edkamb/crowbar-tool.git .
./gradlew assemble
java -jar build/libs/crowbar.jar --full examples/account.abs
```
The expected output should end in the lines
```
...
Crowbar  : Final verification result: true
Crowbar  : Verification time: ...
Crowbar  : Total number of branches: 6
```
On macOS, install Z3 with `brew install z3` instead. 

You can find examples in `./examples/` and `./src/test/resources/`