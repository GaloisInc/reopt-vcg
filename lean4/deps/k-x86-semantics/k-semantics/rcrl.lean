def rcrl1 : instruction :=
  definst "rcrl" $ do
    pattern fun cl (v_2502 : reg (bv 32)) => do
      v_4485 <- getRegister cf;
      v_4488 <- getRegister v_2502;
      v_4490 <- getRegister rcx;
      v_4494 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_4490 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_4496 <- eval (rorHelper (concat (mux (eq v_4485 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4488) (uvalueMInt v_4494) 0);
      v_4498 <- eval (extract v_4494 25 33);
      v_4499 <- eval (eq v_4498 (expression.bv_nat 8 1));
      v_4508 <- eval (eq v_4498 (expression.bv_nat 8 0));
      v_4511 <- getRegister of;
      setRegister (lhs.of_reg v_2502) (extract v_4496 1 33);
      setRegister of (mux (bit_or (bit_and v_4499 (notBool_ (eq (eq (extract v_4496 1 2) (expression.bv_nat 1 1)) (eq (extract v_4496 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4499) (bit_or (bit_and (notBool_ v_4508) undef) (bit_and v_4508 (eq v_4511 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4496 0 1);
      pure ()
    pat_end;
    pattern fun (v_2505 : imm int) (v_2507 : reg (bv 32)) => do
      v_4522 <- getRegister cf;
      v_4525 <- getRegister v_2507;
      v_4530 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_2505 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_4532 <- eval (rorHelper (concat (mux (eq v_4522 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4525) (uvalueMInt v_4530) 0);
      v_4534 <- eval (extract v_4530 25 33);
      v_4535 <- eval (eq v_4534 (expression.bv_nat 8 1));
      v_4544 <- eval (eq v_4534 (expression.bv_nat 8 0));
      v_4547 <- getRegister of;
      setRegister (lhs.of_reg v_2507) (extract v_4532 1 33);
      setRegister of (mux (bit_or (bit_and v_4535 (notBool_ (eq (eq (extract v_4532 1 2) (expression.bv_nat 1 1)) (eq (extract v_4532 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4535) (bit_or (bit_and (notBool_ v_4544) undef) (bit_and v_4544 (eq v_4547 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4532 0 1);
      pure ()
    pat_end;
    pattern fun $0x1 (v_2511 : reg (bv 32)) => do
      v_4558 <- getRegister cf;
      v_4560 <- eval (mux (eq v_4558 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_4561 <- getRegister v_2511;
      v_4562 <- eval (concat v_4560 v_4561);
      v_4565 <- eval (add (bitwidthMInt v_4560) 32);
      v_4566 <- eval (sub v_4565 1);
      v_4570 <- eval (add (lshr v_4562 1) (concat (extract v_4562 v_4566 v_4565) (mi v_4566 0)));
      setRegister (lhs.of_reg v_2511) (extract v_4570 1 33);
      setRegister of (mux (notBool_ (eq (eq (extract v_4570 1 2) (expression.bv_nat 1 1)) (eq (extract v_4570 2 3) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4570 0 1);
      pure ()
    pat_end;
    pattern fun cl (v_2491 : Mem) => do
      v_13710 <- evaluateAddress v_2491;
      v_13711 <- getRegister cf;
      v_13714 <- load v_13710 4;
      v_13716 <- getRegister rcx;
      v_13720 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (extract v_13716 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_13722 <- eval (rorHelper (concat (mux (eq v_13711 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13714) (uvalueMInt v_13720) 0);
      store v_13710 (extract v_13722 1 33) 4;
      v_13726 <- eval (extract v_13720 25 33);
      v_13727 <- eval (eq v_13726 (expression.bv_nat 8 1));
      v_13736 <- eval (eq v_13726 (expression.bv_nat 8 0));
      v_13739 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13727 (notBool_ (eq (eq (extract v_13722 1 2) (expression.bv_nat 1 1)) (eq (extract v_13722 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13727) (bit_or (bit_and (notBool_ v_13736) undef) (bit_and v_13736 (eq v_13739 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13722 0 1);
      pure ()
    pat_end;
    pattern fun (v_2495 : imm int) (v_2494 : Mem) => do
      v_13748 <- evaluateAddress v_2494;
      v_13749 <- getRegister cf;
      v_13752 <- load v_13748 4;
      v_13757 <- eval (urem (concat (expression.bv_nat 25 0) (bv_and (handleImmediateWithSignExtend v_2495 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 33 33));
      v_13759 <- eval (rorHelper (concat (mux (eq v_13749 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13752) (uvalueMInt v_13757) 0);
      store v_13748 (extract v_13759 1 33) 4;
      v_13763 <- eval (extract v_13757 25 33);
      v_13764 <- eval (eq v_13763 (expression.bv_nat 8 1));
      v_13773 <- eval (eq v_13763 (expression.bv_nat 8 0));
      v_13776 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13764 (notBool_ (eq (eq (extract v_13759 1 2) (expression.bv_nat 1 1)) (eq (extract v_13759 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13764) (bit_or (bit_and (notBool_ v_13773) undef) (bit_and v_13773 (eq v_13776 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13759 0 1);
      pure ()
    pat_end
