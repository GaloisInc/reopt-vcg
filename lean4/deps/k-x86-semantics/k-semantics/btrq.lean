def btrq1 : instruction :=
  definst "btrq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (add v_2 (concat (expression.bv_nat 59 0) (bv_and (extract v_3 0 5) (expression.bv_nat 5 7))));
      v_5 <- load v_4 1;
      v_6 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_3 5 8) (expression.bv_nat 3 7)));
      store v_4 (bv_and v_5 (bv_xor (extract (shl (expression.bv_nat 8 1) v_6) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5 v_6) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_1;
      v_3 <- eval (sext (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63)) 64);
      setRegister (lhs.of_reg r64_1) (bv_and v_2 (bv_xor (extract (shl (expression.bv_nat 64 1) v_3) 0 64) (expression.bv_nat 64 18446744073709551615)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 v_3) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r64_0;
      v_4 <- eval (add v_2 (concat (expression.bv_nat 3 0) (extract v_3 0 61)));
      v_5 <- load v_4 1;
      v_6 <- eval (concat (expression.bv_nat 5 0) (extract v_3 61 64));
      store v_4 (bv_and v_5 (bv_xor (extract (shl (expression.bv_nat 8 1) v_6) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5 v_6) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_1;
      v_3 <- getRegister r64_0;
      v_4 <- eval (bv_and v_3 (expression.bv_nat 64 63));
      setRegister (lhs.of_reg r64_1) (bv_and v_2 (bv_xor (extract (shl (expression.bv_nat 64 1) v_4) 0 64) (expression.bv_nat 64 18446744073709551615)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 v_4) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
