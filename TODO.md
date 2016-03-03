# Base Implementation (5)

Working:

  - WLP
  - Z3 integrated using SBV
  - Proving D1
  - Disproving D2

# Array Assignments (1)

Works

# Program Call (2)

Todo:
  - provide environment (in DSL monad) with procedure names and associated pre-/post-conditions
  - extend AST to deal with program calls
  - extend DSL with program call construct
  - handle program call 
    - inserting var-declarations for input and output arguments
    - insert assert/assume pair for specification
    - insert assignments from output arguments to assignment targets of procedure call 
    
# Loop Reduction (1)

Todo:
  - Fixpoint iteration
  - <while>^k
  - verify associated examples
  
# Report & Presentation (1)

Todo:
  - Introduction (describe/motivate problem)
  - Proposed solution
  - Our results (demonstrate how solution solves problem)
  - related works
  - conclusions 
