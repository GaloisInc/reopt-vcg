

/-- Flag indicating some non-zero number of verification conditions failed to be
  verified when passed to an SMT solver. -/
def ExitFlag.verificationFailure : UInt32 := 0b001

/-- Flag indicating an error occured while querying the SMT solver. -/
def ExitFlag.verificationError : UInt32 := 0b010

/-- Flag indicating an error occured while generating verification conditions. -/
def ExitFlag.generationError : UInt32 := 0b100
