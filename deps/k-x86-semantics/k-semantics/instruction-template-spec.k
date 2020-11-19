module INSTRUCTION-TEMPLATE-SPEC
  imports X86-SEMANTICS

  // this property executes one instruction to completion, and binds the results
  // to the `?` variables
  rule
    <k> execinstr((Opcode:Opcode) (Ops:InstructionOperands)) => exit_0 </k>
    <regstate> RegMap => ?RegMap </regstate>
    <leanmemory> MemMap => ?MemMap' </leanmemory>
endmodule

