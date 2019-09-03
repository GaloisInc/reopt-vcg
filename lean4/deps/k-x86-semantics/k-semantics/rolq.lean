def rolq1 : instruction :=
  definst "rolq" $ do
    pattern fun cl (v_2633 : reg (bv 64)) => do
      v_5088 <- getRegister rcx;
      v_5090 <- eval (bv_and (extract v_5088 56 64) (expression.bv_nat 8 63));
      v_5091 <- eval (eq v_5090 (expression.bv_nat 8 0));
      v_5092 <- eval (notBool_ v_5091);
      v_5093 <- getRegister v_2633;
      v_5096 <- eval (rolHelper v_5093 (uvalueMInt (concat (expression.bv_nat 56 0) v_5090)) 0);
      v_5098 <- eval (eq (extract v_5096 63 64) (expression.bv_nat 1 1));
      v_5100 <- getRegister cf;
      v_5105 <- eval (eq v_5090 (expression.bv_nat 8 1));
      v_5113 <- getRegister of;
      setRegister (lhs.of_reg v_2633) v_5096;
      setRegister of (mux (bit_or (bit_and v_5105 (notBool_ (eq (eq (extract v_5096 0 1) (expression.bv_nat 1 1)) v_5098))) (bit_and (notBool_ v_5105) (bit_or (bit_and v_5092 undef) (bit_and v_5091 (eq v_5113 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5092 v_5098) (bit_and v_5091 (eq v_5100 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2636 : imm int) (v_2638 : reg (bv 64)) => do
      v_5124 <- eval (bv_and (handleImmediateWithSignExtend v_2636 8 8) (expression.bv_nat 8 63));
      v_5125 <- eval (eq v_5124 (expression.bv_nat 8 0));
      v_5126 <- eval (notBool_ v_5125);
      v_5127 <- getRegister v_2638;
      v_5130 <- eval (rolHelper v_5127 (uvalueMInt (concat (expression.bv_nat 56 0) v_5124)) 0);
      v_5132 <- eval (eq (extract v_5130 63 64) (expression.bv_nat 1 1));
      v_5134 <- getRegister cf;
      v_5139 <- eval (eq v_5124 (expression.bv_nat 8 1));
      v_5147 <- getRegister of;
      setRegister (lhs.of_reg v_2638) v_5130;
      setRegister of (mux (bit_or (bit_and v_5139 (notBool_ (eq (eq (extract v_5130 0 1) (expression.bv_nat 1 1)) v_5132))) (bit_and (notBool_ v_5139) (bit_or (bit_and v_5126 undef) (bit_and v_5125 (eq v_5147 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5126 v_5132) (bit_and v_5125 (eq v_5134 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2642 : reg (bv 64)) => do
      v_5157 <- getRegister v_2642;
      v_5162 <- eval (add (extract (shl v_5157 1) 0 64) (concat (expression.bv_nat 63 0) (extract v_5157 0 1)));
      v_5163 <- eval (extract v_5162 63 64);
      setRegister (lhs.of_reg v_2642) v_5162;
      setRegister of (mux (notBool_ (eq (eq (extract v_5162 0 1) (expression.bv_nat 1 1)) (eq v_5163 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5163;
      pure ()
    pat_end;
    pattern fun cl (v_2622 : Mem) => do
      v_14373 <- evaluateAddress v_2622;
      v_14374 <- load v_14373 8;
      v_14375 <- getRegister rcx;
      v_14377 <- eval (bv_and (extract v_14375 56 64) (expression.bv_nat 8 63));
      v_14380 <- eval (rolHelper v_14374 (uvalueMInt (concat (expression.bv_nat 56 0) v_14377)) 0);
      store v_14373 v_14380 8;
      v_14382 <- eval (eq v_14377 (expression.bv_nat 8 0));
      v_14383 <- eval (notBool_ v_14382);
      v_14385 <- eval (eq (extract v_14380 63 64) (expression.bv_nat 1 1));
      v_14387 <- getRegister cf;
      v_14392 <- eval (eq v_14377 (expression.bv_nat 8 1));
      v_14400 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14392 (notBool_ (eq (eq (extract v_14380 0 1) (expression.bv_nat 1 1)) v_14385))) (bit_and (notBool_ v_14392) (bit_or (bit_and v_14383 undef) (bit_and v_14382 (eq v_14400 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14383 v_14385) (bit_and v_14382 (eq v_14387 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2626 : imm int) (v_2625 : Mem) => do
      v_14409 <- evaluateAddress v_2625;
      v_14410 <- load v_14409 8;
      v_14412 <- eval (bv_and (handleImmediateWithSignExtend v_2626 8 8) (expression.bv_nat 8 63));
      v_14415 <- eval (rolHelper v_14410 (uvalueMInt (concat (expression.bv_nat 56 0) v_14412)) 0);
      store v_14409 v_14415 8;
      v_14417 <- eval (eq v_14412 (expression.bv_nat 8 0));
      v_14418 <- eval (notBool_ v_14417);
      v_14420 <- eval (eq (extract v_14415 63 64) (expression.bv_nat 1 1));
      v_14422 <- getRegister cf;
      v_14427 <- eval (eq v_14412 (expression.bv_nat 8 1));
      v_14435 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14427 (notBool_ (eq (eq (extract v_14415 0 1) (expression.bv_nat 1 1)) v_14420))) (bit_and (notBool_ v_14427) (bit_or (bit_and v_14418 undef) (bit_and v_14417 (eq v_14435 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14418 v_14420) (bit_and v_14417 (eq v_14422 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
