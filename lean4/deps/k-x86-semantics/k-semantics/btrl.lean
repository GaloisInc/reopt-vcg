def btrl1 : instruction :=
  definst "btrl" $ do
    pattern fun (v_3199 : imm int) (v_3203 : reg (bv 32)) => do
      v_6006 <- getRegister v_3203;
      v_6009 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3199 8 8) (expression.bv_nat 8 31)) 32);
      setRegister (lhs.of_reg v_3203) (bv_and v_6006 (bv_xor (extract (shl (expression.bv_nat 32 1) v_6009) 0 32) (expression.bv_nat 32 4294967295)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6006 v_6009) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3207 : reg (bv 32)) (v_3208 : reg (bv 32)) => do
      v_6022 <- getRegister v_3208;
      v_6023 <- getRegister v_3207;
      v_6024 <- eval (bv_and v_6023 (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_3208) (bv_and v_6022 (bv_xor (extract (shl (expression.bv_nat 32 1) v_6024) 0 32) (expression.bv_nat 32 4294967295)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6022 v_6024) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3191 : imm int) (v_3194 : Mem) => do
      v_10585 <- evaluateAddress v_3194;
      v_10586 <- eval (handleImmediateWithSignExtend v_3191 8 8);
      v_10590 <- eval (add v_10585 (concat (expression.bv_nat 59 0) (bv_and (extract v_10586 0 5) (expression.bv_nat 5 3))));
      v_10591 <- load v_10590 1;
      v_10594 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10586 5 8) (expression.bv_nat 3 7)));
      store v_10590 (bv_and v_10591 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10594) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10591 v_10594) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3198 : reg (bv 32)) (v_3197 : Mem) => do
      v_10607 <- evaluateAddress v_3197;
      v_10608 <- getRegister v_3198;
      v_10612 <- eval (add v_10607 (concat (expression.bv_nat 3 0) (extract (sext v_10608 64) 0 61)));
      v_10613 <- load v_10612 1;
      v_10615 <- eval (concat (expression.bv_nat 5 0) (extract v_10608 29 32));
      store v_10612 (bv_and v_10613 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10615) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10613 v_10615) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
