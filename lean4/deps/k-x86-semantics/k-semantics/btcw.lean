def btcw1 : instruction :=
  definst "btcw" $ do
    pattern fun (v_3120 : imm int) (v_3118 : reg (bv 16)) => do
      v_6030 <- getRegister v_3118;
      v_6033 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3120 8 8) (expression.bv_nat 8 15)) 16);
      setRegister (lhs.of_reg v_3118) (bv_xor v_6030 (extract (shl (expression.bv_nat 16 1) v_6033) 0 16));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6030 v_6033) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3123 : reg (bv 16)) (v_3124 : reg (bv 16)) => do
      v_6045 <- getRegister v_3124;
      v_6046 <- getRegister v_3123;
      v_6047 <- eval (bv_and v_6046 (expression.bv_nat 16 15));
      setRegister (lhs.of_reg v_3124) (bv_xor v_6045 (extract (shl (expression.bv_nat 16 1) v_6047) 0 16));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6045 v_6047) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3111 : imm int) (v_3113 : Mem) => do
      v_10820 <- evaluateAddress v_3113;
      v_10821 <- eval (handleImmediateWithSignExtend v_3111 8 8);
      v_10825 <- eval (add v_10820 (concat (expression.bv_nat 59 0) (bv_and (extract v_10821 0 5) (expression.bv_nat 5 1))));
      v_10826 <- load v_10825 1;
      v_10829 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10821 5 8) (expression.bv_nat 3 7)));
      store v_10825 (bv_xor v_10826 (extract (shl (expression.bv_nat 8 1) v_10829) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10826 v_10829) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3114 : reg (bv 16)) (v_3117 : Mem) => do
      v_10841 <- evaluateAddress v_3117;
      v_10842 <- getRegister v_3114;
      v_10846 <- eval (add v_10841 (concat (expression.bv_nat 3 0) (extract (sext v_10842 64) 0 61)));
      v_10847 <- load v_10846 1;
      v_10849 <- eval (concat (expression.bv_nat 5 0) (extract v_10842 13 16));
      store v_10846 (bv_xor v_10847 (extract (shl (expression.bv_nat 8 1) v_10849) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10847 v_10849) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
