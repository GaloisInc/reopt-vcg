def rcrb1 : instruction :=
  definst "rcrb" $ do
    pattern fun cl (v_2466 : reg (bv 8)) => do
      v_4279 <- getRegister cf;
      v_4282 <- getRegister v_2466;
      v_4284 <- getRegister rcx;
      v_4288 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_4284 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_4290 <- eval (rorHelper (concat (mux (eq v_4279 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4282) (uvalueMInt v_4288) 0);
      v_4292 <- eval (extract v_4288 1 9);
      v_4293 <- eval (eq v_4292 (expression.bv_nat 8 1));
      v_4302 <- eval (eq v_4292 (expression.bv_nat 8 0));
      v_4305 <- getRegister of;
      setRegister (lhs.of_reg v_2466) (extract v_4290 1 9);
      setRegister of (mux (bit_or (bit_and v_4293 (notBool_ (eq (eq (extract v_4290 1 2) (expression.bv_nat 1 1)) (eq (extract v_4290 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4293) (bit_or (bit_and (notBool_ v_4302) undef) (bit_and v_4302 (eq v_4305 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4290 0 1);
      pure ()
    pat_end;
    pattern fun (v_2469 : imm int) (v_2471 : reg (bv 8)) => do
      v_4316 <- getRegister cf;
      v_4319 <- getRegister v_2471;
      v_4324 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_2469 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_4326 <- eval (rorHelper (concat (mux (eq v_4316 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4319) (uvalueMInt v_4324) 0);
      v_4328 <- eval (extract v_4324 1 9);
      v_4329 <- eval (eq v_4328 (expression.bv_nat 8 1));
      v_4338 <- eval (eq v_4328 (expression.bv_nat 8 0));
      v_4341 <- getRegister of;
      setRegister (lhs.of_reg v_2471) (extract v_4326 1 9);
      setRegister of (mux (bit_or (bit_and v_4329 (notBool_ (eq (eq (extract v_4326 1 2) (expression.bv_nat 1 1)) (eq (extract v_4326 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4329) (bit_or (bit_and (notBool_ v_4338) undef) (bit_and v_4338 (eq v_4341 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4326 0 1);
      pure ()
    pat_end;
    pattern fun $0x1 (v_2475 : reg (bv 8)) => do
      v_4352 <- getRegister cf;
      v_4354 <- eval (mux (eq v_4352 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_4355 <- getRegister v_2475;
      v_4356 <- eval (concat v_4354 v_4355);
      v_4359 <- eval (add (bitwidthMInt v_4354) 8);
      v_4360 <- eval (sub v_4359 1);
      v_4364 <- eval (add (lshr v_4356 1) (concat (extract v_4356 v_4360 v_4359) (mi v_4360 0)));
      setRegister (lhs.of_reg v_2475) (extract v_4364 1 9);
      setRegister of (mux (notBool_ (eq (eq (extract v_4364 1 2) (expression.bv_nat 1 1)) (eq (extract v_4364 2 3) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4364 0 1);
      pure ()
    pat_end;
    pattern fun cl (v_2455 : Mem) => do
      v_13583 <- evaluateAddress v_2455;
      v_13584 <- getRegister cf;
      v_13587 <- load v_13583 1;
      v_13589 <- getRegister rcx;
      v_13593 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_13589 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_13595 <- eval (rorHelper (concat (mux (eq v_13584 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13587) (uvalueMInt v_13593) 0);
      store v_13583 (extract v_13595 1 9) 1;
      v_13599 <- eval (extract v_13593 1 9);
      v_13600 <- eval (eq v_13599 (expression.bv_nat 8 1));
      v_13609 <- eval (eq v_13599 (expression.bv_nat 8 0));
      v_13612 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13600 (notBool_ (eq (eq (extract v_13595 1 2) (expression.bv_nat 1 1)) (eq (extract v_13595 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13600) (bit_or (bit_and (notBool_ v_13609) undef) (bit_and v_13609 (eq v_13612 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13595 0 1);
      pure ()
    pat_end;
    pattern fun (v_2459 : imm int) (v_2458 : Mem) => do
      v_13621 <- evaluateAddress v_2458;
      v_13622 <- getRegister cf;
      v_13625 <- load v_13621 1;
      v_13630 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_2459 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_13632 <- eval (rorHelper (concat (mux (eq v_13622 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13625) (uvalueMInt v_13630) 0);
      store v_13621 (extract v_13632 1 9) 1;
      v_13636 <- eval (extract v_13630 1 9);
      v_13637 <- eval (eq v_13636 (expression.bv_nat 8 1));
      v_13646 <- eval (eq v_13636 (expression.bv_nat 8 0));
      v_13649 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13637 (notBool_ (eq (eq (extract v_13632 1 2) (expression.bv_nat 1 1)) (eq (extract v_13632 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13637) (bit_or (bit_and (notBool_ v_13646) undef) (bit_and v_13646 (eq v_13649 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13632 0 1);
      pure ()
    pat_end
