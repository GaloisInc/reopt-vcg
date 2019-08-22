module INSTRUCTION-TEMPLATE-SPEC
  imports X86-SEMANTICS

  rule
    <k> execinstr((Opcode:Opcode) (Ops:InstructionOperands)) => exit_0 </k>
    <regstate> RegMap => ?RegMap' </regstate>
    <leanmemory> MemMap => ?MemMap' </leanmemory>
endmodule

