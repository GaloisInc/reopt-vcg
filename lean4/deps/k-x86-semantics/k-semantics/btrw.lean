def btrw1 : instruction :=
  definst "btrw" $ do
    pattern fun (v_3210 : imm int) (v_3208 : reg (bv 16)) => do
      v_6203 <- getRegister v_3208;
      v_6206 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3210 8 8) (expression.bv_nat 8 15)) 16);
      setRegister (lhs.of_reg v_3208) (bv_and v_6203 (bv_xor (extract (shl (expression.bv_nat 16 1) v_6206) 0 16) (expression.bv_nat 16 65535)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6203 v_6206) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3213 : reg (bv 16)) (v_3214 : reg (bv 16)) => do
      v_6219 <- getRegister v_3214;
      v_6220 <- getRegister v_3213;
      v_6221 <- eval (bv_and v_6220 (expression.bv_nat 16 15));
      setRegister (lhs.of_reg v_3214) (bv_and v_6219 (bv_xor (extract (shl (expression.bv_nat 16 1) v_6221) 0 16) (expression.bv_nat 16 65535)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6219 v_6221) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3201 : imm int) (v_3203 : Mem) => do
      v_10946 <- evaluateAddress v_3203;
      v_10947 <- eval (handleImmediateWithSignExtend v_3201 8 8);
      v_10951 <- eval (add v_10946 (concat (expression.bv_nat 59 0) (bv_and (extract v_10947 0 5) (expression.bv_nat 5 1))));
      v_10952 <- load v_10951 1;
      v_10955 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10947 5 8) (expression.bv_nat 3 7)));
      store v_10951 (bv_and v_10952 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10955) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10952 v_10955) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3204 : reg (bv 16)) (v_3207 : Mem) => do
      v_10968 <- evaluateAddress v_3207;
      v_10969 <- getRegister v_3204;
      v_10973 <- eval (add v_10968 (concat (expression.bv_nat 3 0) (extract (sext v_10969 64) 0 61)));
      v_10974 <- load v_10973 1;
      v_10976 <- eval (concat (expression.bv_nat 5 0) (extract v_10969 13 16));
      store v_10973 (bv_and v_10974 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10976) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10974 v_10976) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
