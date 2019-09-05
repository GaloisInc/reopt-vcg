def rcrq1 : instruction :=
  definst "rcrq" $ do
    pattern fun cl (v_2578 : reg (bv 64)) => do
      v_4522 <- getRegister rcx;
      v_4526 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_4522 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4527 <- eval (extract v_4526 57 65);
      v_4528 <- eval (eq v_4527 (expression.bv_nat 8 1));
      v_4529 <- getRegister cf;
      v_4532 <- getRegister v_2578;
      v_4534 <- eval (ror (concat (mux (eq v_4529 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4532) v_4526);
      v_4541 <- eval (eq v_4527 (expression.bv_nat 8 0));
      v_4544 <- getRegister of;
      setRegister (lhs.of_reg v_2578) (extract v_4534 1 65);
      setRegister cf (isBitSet v_4534 0);
      setRegister of (bit_or (bit_and v_4528 (notBool_ (eq (isBitSet v_4534 1) (isBitSet v_4534 2)))) (bit_and (notBool_ v_4528) (bit_or (bit_and (notBool_ v_4541) undef) (bit_and v_4541 (eq v_4544 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2581 : imm int) (v_2583 : reg (bv 64)) => do
      v_4558 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2581 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4559 <- eval (extract v_4558 57 65);
      v_4560 <- eval (eq v_4559 (expression.bv_nat 8 1));
      v_4561 <- getRegister cf;
      v_4564 <- getRegister v_2583;
      v_4566 <- eval (ror (concat (mux (eq v_4561 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4564) v_4558);
      v_4573 <- eval (eq v_4559 (expression.bv_nat 8 0));
      v_4576 <- getRegister of;
      setRegister (lhs.of_reg v_2583) (extract v_4566 1 65);
      setRegister cf (isBitSet v_4566 0);
      setRegister of (bit_or (bit_and v_4560 (notBool_ (eq (isBitSet v_4566 1) (isBitSet v_4566 2)))) (bit_and (notBool_ v_4560) (bit_or (bit_and (notBool_ v_4573) undef) (bit_and v_4573 (eq v_4576 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2567 : Mem) => do
      v_12014 <- evaluateAddress v_2567;
      v_12015 <- getRegister cf;
      v_12018 <- load v_12014 8;
      v_12020 <- getRegister rcx;
      v_12024 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_12020 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_12025 <- eval (ror (concat (mux (eq v_12015 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_12018) v_12024);
      store v_12014 (extract v_12025 1 65) 8;
      v_12028 <- eval (extract v_12024 57 65);
      v_12029 <- eval (eq v_12028 (expression.bv_nat 8 1));
      v_12036 <- eval (eq v_12028 (expression.bv_nat 8 0));
      v_12039 <- getRegister of;
      setRegister cf (isBitSet v_12025 0);
      setRegister of (bit_or (bit_and v_12029 (notBool_ (eq (isBitSet v_12025 1) (isBitSet v_12025 2)))) (bit_and (notBool_ v_12029) (bit_or (bit_and (notBool_ v_12036) undef) (bit_and v_12036 (eq v_12039 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2570 : imm int) (v_2571 : Mem) => do
      v_12048 <- evaluateAddress v_2571;
      v_12049 <- getRegister cf;
      v_12052 <- load v_12048 8;
      v_12057 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2570 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_12058 <- eval (ror (concat (mux (eq v_12049 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_12052) v_12057);
      store v_12048 (extract v_12058 1 65) 8;
      v_12061 <- eval (extract v_12057 57 65);
      v_12062 <- eval (eq v_12061 (expression.bv_nat 8 1));
      v_12069 <- eval (eq v_12061 (expression.bv_nat 8 0));
      v_12072 <- getRegister of;
      setRegister cf (isBitSet v_12058 0);
      setRegister of (bit_or (bit_and v_12062 (notBool_ (eq (isBitSet v_12058 1) (isBitSet v_12058 2)))) (bit_and (notBool_ v_12062) (bit_or (bit_and (notBool_ v_12069) undef) (bit_and v_12069 (eq v_12072 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
