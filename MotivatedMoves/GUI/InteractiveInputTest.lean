import MotivatedMoves.GUI.InteractiveInput

open Lean ProofWidgets Jsx

#html <Form>
    <input name="query" />
    <button type="submit">Go</button>
  </Form>

#eval show IO _ from formRef.get