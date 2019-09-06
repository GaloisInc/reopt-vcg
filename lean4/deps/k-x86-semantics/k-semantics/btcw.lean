def btcw1 : instruction :=
  definst "btcw" $ do
    pattern fun (v_3145 : imm int) (v_3148 : reg (bv 16)) => do
      v_5911 <- getRegister v_3148;
      v_5914 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3145 8 8) (expression.bv_nat 8 15)) 16);
      setRegister (lhs.of_reg v_3148) (bv_xor v_5911 (extract (shl (expression.bv_nat 16 1) v_5914) 0 16));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5911 v_5914) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3152 : reg (bv 16)) (v_3153 : reg (bv 16)) => do
      v_5926 <- getRegister v_3153;
      v_5927 <- getRegister v_3152;
      v_5928 <- eval (bv_and v_5927 (expression.bv_nat 16 15));
      setRegister (lhs.of_reg v_3153) (bv_xor v_5926 (extract (shl (expression.bv_nat 16 1) v_5928) 0 16));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5926 v_5928) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3137 : imm int) (v_3140 : Mem) => do
      v_10544 <- evaluateAddress v_3140;
      v_10545 <- eval (handleImmediateWithSignExtend v_3137 8 8);
      v_10549 <- eval (add v_10544 (concat (expression.bv_nat 59 0) (bv_and (extract v_10545 0 5) (expression.bv_nat 5 1))));
      v_10550 <- load v_10549 1;
      v_10553 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10545 5 8) (expression.bv_nat 3 7)));
      store v_10549 (bv_xor v_10550 (extract (shl (expression.bv_nat 8 1) v_10553) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10550 v_10553) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3144 : reg (bv 16)) (v_3143 : Mem) => do
      v_10565 <- evaluateAddress v_3143;
      v_10566 <- getRegister v_3144;
      v_10570 <- eval (add v_10565 (concat (expression.bv_nat 3 0) (extract (sext v_10566 64) 0 61)));
      v_10571 <- load v_10570 1;
      v_10573 <- eval (concat (expression.bv_nat 5 0) (extract v_10566 13 16));
      store v_10570 (bv_xor v_10571 (extract (shl (expression.bv_nat 8 1) v_10573) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10571 v_10573) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
