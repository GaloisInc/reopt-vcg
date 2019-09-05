def rolw1 : instruction :=
  definst "rolw" $ do
    pattern fun cl (v_2706 : reg (bv 16)) => do
      v_5008 <- getRegister rcx;
      v_5010 <- eval (bv_and (extract v_5008 56 64) (expression.bv_nat 8 31));
      v_5011 <- eval (eq v_5010 (expression.bv_nat 8 1));
      v_5012 <- getRegister v_2706;
      v_5014 <- eval (rol v_5012 (concat (expression.bv_nat 8 0) v_5010));
      v_5016 <- eval (isBitSet v_5014 15);
      v_5021 <- eval (eq v_5010 (expression.bv_nat 8 0));
      v_5022 <- eval (notBool_ v_5021);
      v_5024 <- getRegister of;
      v_5031 <- getRegister cf;
      setRegister (lhs.of_reg v_2706) v_5014;
      setRegister cf (bit_or (bit_and v_5022 v_5016) (bit_and v_5021 (eq v_5031 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5011 (notBool_ (eq (isBitSet v_5014 0) v_5016))) (bit_and (notBool_ v_5011) (bit_or (bit_and v_5022 undef) (bit_and v_5021 (eq v_5024 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2713 : imm int) (v_2710 : reg (bv 16)) => do
      v_5039 <- eval (bv_and (handleImmediateWithSignExtend v_2713 8 8) (expression.bv_nat 8 31));
      v_5040 <- eval (eq v_5039 (expression.bv_nat 8 1));
      v_5041 <- getRegister v_2710;
      v_5043 <- eval (rol v_5041 (concat (expression.bv_nat 8 0) v_5039));
      v_5045 <- eval (isBitSet v_5043 15);
      v_5050 <- eval (eq v_5039 (expression.bv_nat 8 0));
      v_5051 <- eval (notBool_ v_5050);
      v_5053 <- getRegister of;
      v_5060 <- getRegister cf;
      setRegister (lhs.of_reg v_2710) v_5043;
      setRegister cf (bit_or (bit_and v_5051 v_5045) (bit_and v_5050 (eq v_5060 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5040 (notBool_ (eq (isBitSet v_5043 0) v_5045))) (bit_and (notBool_ v_5040) (bit_or (bit_and v_5051 undef) (bit_and v_5050 (eq v_5053 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2698 : Mem) => do
      v_12454 <- evaluateAddress v_2698;
      v_12455 <- load v_12454 2;
      v_12456 <- getRegister rcx;
      v_12458 <- eval (bv_and (extract v_12456 56 64) (expression.bv_nat 8 31));
      v_12460 <- eval (rol v_12455 (concat (expression.bv_nat 8 0) v_12458));
      store v_12454 v_12460 2;
      v_12462 <- eval (eq v_12458 (expression.bv_nat 8 1));
      v_12464 <- eval (isBitSet v_12460 15);
      v_12469 <- eval (eq v_12458 (expression.bv_nat 8 0));
      v_12470 <- eval (notBool_ v_12469);
      v_12472 <- getRegister of;
      v_12479 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12470 v_12464) (bit_and v_12469 (eq v_12479 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12462 (notBool_ (eq (isBitSet v_12460 0) v_12464))) (bit_and (notBool_ v_12462) (bit_or (bit_and v_12470 undef) (bit_and v_12469 (eq v_12472 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2701 : imm int) (v_2702 : Mem) => do
      v_12485 <- evaluateAddress v_2702;
      v_12486 <- load v_12485 2;
      v_12488 <- eval (bv_and (handleImmediateWithSignExtend v_2701 8 8) (expression.bv_nat 8 31));
      v_12490 <- eval (rol v_12486 (concat (expression.bv_nat 8 0) v_12488));
      store v_12485 v_12490 2;
      v_12492 <- eval (eq v_12488 (expression.bv_nat 8 1));
      v_12494 <- eval (isBitSet v_12490 15);
      v_12499 <- eval (eq v_12488 (expression.bv_nat 8 0));
      v_12500 <- eval (notBool_ v_12499);
      v_12502 <- getRegister of;
      v_12509 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12500 v_12494) (bit_and v_12499 (eq v_12509 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12492 (notBool_ (eq (isBitSet v_12490 0) v_12494))) (bit_and (notBool_ v_12492) (bit_or (bit_and v_12500 undef) (bit_and v_12499 (eq v_12502 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
