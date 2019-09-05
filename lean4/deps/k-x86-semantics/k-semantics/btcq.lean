def btcq1 : instruction :=
  definst "btcq" $ do
    pattern fun (v_3101 : imm int) (v_3104 : reg (bv 64)) => do
      v_5993 <- getRegister v_3104;
      v_5996 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3101 8 8) (expression.bv_nat 8 63)) 64);
      setRegister (lhs.of_reg v_3104) (bv_xor v_5993 (extract (shl (expression.bv_nat 64 1) v_5996) 0 64));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5993 v_5996) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3108 : reg (bv 64)) (v_3109 : reg (bv 64)) => do
      v_6008 <- getRegister v_3109;
      v_6009 <- getRegister v_3108;
      v_6010 <- eval (bv_and v_6009 (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_3109) (bv_xor v_6008 (extract (shl (expression.bv_nat 64 1) v_6010) 0 64));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6008 v_6010) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3093 : imm int) (v_3095 : Mem) => do
      v_10780 <- evaluateAddress v_3095;
      v_10781 <- eval (handleImmediateWithSignExtend v_3093 8 8);
      v_10785 <- eval (add v_10780 (concat (expression.bv_nat 59 0) (bv_and (extract v_10781 0 5) (expression.bv_nat 5 7))));
      v_10786 <- load v_10785 1;
      v_10789 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10781 5 8) (expression.bv_nat 3 7)));
      store v_10785 (bv_xor v_10786 (extract (shl (expression.bv_nat 8 1) v_10789) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10786 v_10789) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3099 : reg (bv 64)) (v_3098 : Mem) => do
      v_10801 <- evaluateAddress v_3098;
      v_10802 <- getRegister v_3099;
      v_10805 <- eval (add v_10801 (concat (expression.bv_nat 3 0) (extract v_10802 0 61)));
      v_10806 <- load v_10805 1;
      v_10808 <- eval (concat (expression.bv_nat 5 0) (extract v_10802 61 64));
      store v_10805 (bv_xor v_10806 (extract (shl (expression.bv_nat 8 1) v_10808) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10806 v_10808) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
