def rorq1 : instruction :=
  definst "rorq" $ do
    pattern fun cl (v_2791 : reg (bv 64)) => do
      v_5306 <- getRegister rcx;
      v_5308 <- eval (bv_and (extract v_5306 56 64) (expression.bv_nat 8 63));
      v_5309 <- eval (eq v_5308 (expression.bv_nat 8 1));
      v_5310 <- getRegister v_2791;
      v_5312 <- eval (ror v_5310 (concat (expression.bv_nat 56 0) v_5308));
      v_5313 <- eval (isBitSet v_5312 0);
      v_5319 <- eval (eq v_5308 (expression.bv_nat 8 0));
      v_5320 <- eval (notBool_ v_5319);
      v_5322 <- getRegister of;
      v_5329 <- getRegister cf;
      setRegister (lhs.of_reg v_2791) v_5312;
      setRegister cf (bit_or (bit_and v_5320 v_5313) (bit_and v_5319 (eq v_5329 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5309 (notBool_ (eq v_5313 (isBitSet v_5312 1)))) (bit_and (notBool_ v_5309) (bit_or (bit_and v_5320 undef) (bit_and v_5319 (eq v_5322 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2794 : imm int) (v_2796 : reg (bv 64)) => do
      v_5337 <- eval (bv_and (handleImmediateWithSignExtend v_2794 8 8) (expression.bv_nat 8 63));
      v_5338 <- eval (eq v_5337 (expression.bv_nat 8 1));
      v_5339 <- getRegister v_2796;
      v_5341 <- eval (ror v_5339 (concat (expression.bv_nat 56 0) v_5337));
      v_5342 <- eval (isBitSet v_5341 0);
      v_5348 <- eval (eq v_5337 (expression.bv_nat 8 0));
      v_5349 <- eval (notBool_ v_5348);
      v_5351 <- getRegister of;
      v_5358 <- getRegister cf;
      setRegister (lhs.of_reg v_2796) v_5341;
      setRegister cf (bit_or (bit_and v_5349 v_5342) (bit_and v_5348 (eq v_5358 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5338 (notBool_ (eq v_5342 (isBitSet v_5341 1)))) (bit_and (notBool_ v_5338) (bit_or (bit_and v_5349 undef) (bit_and v_5348 (eq v_5351 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2780 : Mem) => do
      v_12695 <- evaluateAddress v_2780;
      v_12696 <- load v_12695 8;
      v_12697 <- getRegister rcx;
      v_12699 <- eval (bv_and (extract v_12697 56 64) (expression.bv_nat 8 63));
      v_12701 <- eval (ror v_12696 (concat (expression.bv_nat 56 0) v_12699));
      store v_12695 v_12701 8;
      v_12703 <- eval (eq v_12699 (expression.bv_nat 8 1));
      v_12704 <- eval (isBitSet v_12701 0);
      v_12710 <- eval (eq v_12699 (expression.bv_nat 8 0));
      v_12711 <- eval (notBool_ v_12710);
      v_12713 <- getRegister of;
      v_12720 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12711 v_12704) (bit_and v_12710 (eq v_12720 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12703 (notBool_ (eq v_12704 (isBitSet v_12701 1)))) (bit_and (notBool_ v_12703) (bit_or (bit_and v_12711 undef) (bit_and v_12710 (eq v_12713 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2783 : imm int) (v_2784 : Mem) => do
      v_12726 <- evaluateAddress v_2784;
      v_12727 <- load v_12726 8;
      v_12729 <- eval (bv_and (handleImmediateWithSignExtend v_2783 8 8) (expression.bv_nat 8 63));
      v_12731 <- eval (ror v_12727 (concat (expression.bv_nat 56 0) v_12729));
      store v_12726 v_12731 8;
      v_12733 <- eval (eq v_12729 (expression.bv_nat 8 1));
      v_12734 <- eval (isBitSet v_12731 0);
      v_12740 <- eval (eq v_12729 (expression.bv_nat 8 0));
      v_12741 <- eval (notBool_ v_12740);
      v_12743 <- getRegister of;
      v_12750 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12741 v_12734) (bit_and v_12740 (eq v_12750 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12733 (notBool_ (eq v_12734 (isBitSet v_12731 1)))) (bit_and (notBool_ v_12733) (bit_or (bit_and v_12741 undef) (bit_and v_12740 (eq v_12743 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
