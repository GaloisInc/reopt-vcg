def btcq1 : instruction :=
  definst "btcq" $ do
    pattern fun (v_3127 : imm int) (v_3130 : reg (bv 64)) => do
      v_5874 <- getRegister v_3130;
      v_5877 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3127 8 8) (expression.bv_nat 8 63)) 64);
      setRegister (lhs.of_reg v_3130) (bv_xor v_5874 (extract (shl (expression.bv_nat 64 1) v_5877) 0 64));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5874 v_5877) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3134 : reg (bv 64)) (v_3135 : reg (bv 64)) => do
      v_5889 <- getRegister v_3135;
      v_5890 <- getRegister v_3134;
      v_5891 <- eval (bv_and v_5890 (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_3135) (bv_xor v_5889 (extract (shl (expression.bv_nat 64 1) v_5891) 0 64));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5889 v_5891) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3119 : imm int) (v_3122 : Mem) => do
      v_10504 <- evaluateAddress v_3122;
      v_10505 <- eval (handleImmediateWithSignExtend v_3119 8 8);
      v_10509 <- eval (add v_10504 (concat (expression.bv_nat 59 0) (bv_and (extract v_10505 0 5) (expression.bv_nat 5 7))));
      v_10510 <- load v_10509 1;
      v_10513 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10505 5 8) (expression.bv_nat 3 7)));
      store v_10509 (bv_xor v_10510 (extract (shl (expression.bv_nat 8 1) v_10513) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10510 v_10513) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3126 : reg (bv 64)) (v_3125 : Mem) => do
      v_10525 <- evaluateAddress v_3125;
      v_10526 <- getRegister v_3126;
      v_10529 <- eval (add v_10525 (concat (expression.bv_nat 3 0) (extract v_10526 0 61)));
      v_10530 <- load v_10529 1;
      v_10532 <- eval (concat (expression.bv_nat 5 0) (extract v_10526 61 64));
      store v_10529 (bv_xor v_10530 (extract (shl (expression.bv_nat 8 1) v_10532) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10530 v_10532) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
