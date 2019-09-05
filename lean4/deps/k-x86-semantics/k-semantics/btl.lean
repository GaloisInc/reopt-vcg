def btl1 : instruction :=
  definst "btl" $ do
    pattern fun (v_3137 : imm int) (v_3139 : reg (bv 32)) => do
      v_6067 <- getRegister v_3139;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6067 (sext (bv_and (handleImmediateWithSignExtend v_3137 8 8) (expression.bv_nat 8 31)) 32)) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3143 : reg (bv 32)) (v_3144 : reg (bv 32)) => do
      v_6078 <- getRegister v_3144;
      v_6079 <- getRegister v_3143;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6078 (bv_and v_6079 (expression.bv_nat 32 31))) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3129 : imm int) (v_3131 : Mem) => do
      v_9456 <- evaluateAddress v_3131;
      v_9457 <- eval (handleImmediateWithSignExtend v_3129 8 8);
      v_9462 <- load (add v_9456 (concat (expression.bv_nat 59 0) (bv_and (extract v_9457 0 5) (expression.bv_nat 5 3)))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9462 (concat (expression.bv_nat 5 0) (bv_and (extract v_9457 5 8) (expression.bv_nat 3 7)))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3134 : reg (bv 32)) (v_3135 : Mem) => do
      v_9473 <- evaluateAddress v_3135;
      v_9474 <- getRegister v_3134;
      v_9479 <- load (add v_9473 (concat (expression.bv_nat 3 0) (extract (sext v_9474 64) 0 61))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_9479 (concat (expression.bv_nat 5 0) (extract v_9474 29 32))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
