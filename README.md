# Human-oriented tactics in Lean

## Setup
1. Download VSCode.
2. Install Lean4 along with the Lean4 VSCode extension following [these instructions](https://leanprover.github.io/lean4/doc/quickstart.html).  If `#eval Lean.versionString` gives you a Lean version in VSCode, that’s working correctly.  If not, type `elan show` in a terminal to check if Lean4 has been installed at all.
3. `git clone` this repository.
4. Open the folder of this repository and run the following commands (as described [here](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)):
	```
	curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
	lake update
	lake exe cache get
	```
	This will download Mathlib4 including its cache files which you will then find in the folder `lake-packages`.
5. Restart the Lean server: `VSCode > Command-Shift-P > Lean 4: Restart`.
6. Test that your install of Mathlib has worked. For example, you could create a file like this: 
	```
	import Mathlib.Data.Vector.Basic
	
	#check Vector
	```
	Make sure the language of that VSCode file (in the bottom-right-hand corner of VSCode) says `lean4` rather than `lean`. 
	It might take a while for Lean4 to build Mathlib in the background, you should see an info text that tells you the file that is currently being built. 
7. (Temporary) In order to see the custom rendering of the infoview, a custom version of the Lean 4 VSCode extension is required. It can be found and install from the `widget\lean4fork-0.0.111.vsix` file after pressing `Command-Shift-P > Extensions : Install from VSIX...` and then disabling the original Lean 4 VSCode extension.