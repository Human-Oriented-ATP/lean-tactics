# Human-oriented tactics in Lean

## Lean 4 Setup
1. Download VSCode.
2. Install Lean4 along with the Lean4 VSCode extension following [these instructions](https://leanprover.github.io/lean4/doc/quickstart.html).  If `#eval Lean.versionString` gives you a Lean version in VSCode, that’s working correctly.  If not, type `elan show` in terminal to check if Lean4 has installed at all.
3. `git clone` this repository.
4. Open the `lean4` folder of this repository and run `lake update` inside it. This will download Mathlib4 which you will then find in the folder `lake-packages`.
5. Restart the Lean server: `VSCode > Command-Shift-P > Lean 4: Restart`.
6. Test that your install of Mathlib has worked. For example, you could create a file like this: 
	```
	import Mathlib.Data.Vector.Basic
	
	#check Vector
	```
	It might take a while for Lean4 to build Mathlib in the background, you should see an info text that tells you the file that is currently being built. 
8. Download the Mathlib cache by running `lake exe cache get`.

## Tactics written so far in Lean 4

