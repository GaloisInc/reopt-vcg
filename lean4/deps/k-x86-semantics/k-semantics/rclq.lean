def rclq1 : instruction :=
  definst "rclq" $ do
    pattern fun cl (v_2455 : reg (bv 64)) => do
      v_4050 <- getRegister rcx;
      v_4054 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_4050 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4055 <- eval (extract v_4054 57 65);
      v_4056 <- eval (eq v_4055 (expression.bv_nat 8 1));
      v_4057 <- getRegister cf;
      v_4060 <- getRegister v_2455;
      v_4062 <- eval (rol (concat (mux (eq v_4057 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4060) v_4054);
      v_4063 <- eval (isBitSet v_4062 0);
      v_4069 <- eval (eq v_4055 (expression.bv_nat 8 0));
      v_4072 <- getRegister of;
      setRegister (lhs.of_reg v_2455) (extract v_4062 1 65);
      setRegister cf v_4063;
      setRegister of (bit_or (bit_and v_4056 (notBool_ (eq v_4063 (isBitSet v_4062 1)))) (bit_and (notBool_ v_4056) (bit_or (bit_and (notBool_ v_4069) undef) (bit_and v_4069 (eq v_4072 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2458 : imm int) (v_2460 : reg (bv 64)) => do
      v_4085 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2458 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4086 <- eval (extract v_4085 57 65);
      v_4087 <- eval (eq v_4086 (expression.bv_nat 8 1));
      v_4088 <- getRegister cf;
      v_4091 <- getRegister v_2460;
      v_4093 <- eval (rol (concat (mux (eq v_4088 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4091) v_4085);
      v_4094 <- eval (isBitSet v_4093 0);
      v_4100 <- eval (eq v_4086 (expression.bv_nat 8 0));
      v_4103 <- getRegister of;
      setRegister (lhs.of_reg v_2460) (extract v_4093 1 65);
      setRegister cf v_4094;
      setRegister of (bit_or (bit_and v_4087 (notBool_ (eq v_4094 (isBitSet v_4093 1)))) (bit_and (notBool_ v_4087) (bit_or (bit_and (notBool_ v_4100) undef) (bit_and v_4100 (eq v_4103 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2444 : Mem) => do
      v_11626 <- evaluateAddress v_2444;
      v_11627 <- getRegister cf;
      v_11630 <- load v_11626 8;
      v_11632 <- getRegister rcx;
      v_11636 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_11632 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_11637 <- eval (rol (concat (mux (eq v_11627 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11630) v_11636);
      store v_11626 (extract v_11637 1 65) 8;
      v_11640 <- eval (extract v_11636 57 65);
      v_11641 <- eval (eq v_11640 (expression.bv_nat 8 1));
      v_11642 <- eval (isBitSet v_11637 0);
      v_11648 <- eval (eq v_11640 (expression.bv_nat 8 0));
      v_11651 <- getRegister of;
      setRegister cf v_11642;
      setRegister of (bit_or (bit_and v_11641 (notBool_ (eq v_11642 (isBitSet v_11637 1)))) (bit_and (notBool_ v_11641) (bit_or (bit_and (notBool_ v_11648) undef) (bit_and v_11648 (eq v_11651 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2447 : imm int) (v_2448 : Mem) => do
      v_11659 <- evaluateAddress v_2448;
      v_11660 <- getRegister cf;
      v_11663 <- load v_11659 8;
      v_11668 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2447 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_11669 <- eval (rol (concat (mux (eq v_11660 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_11663) v_11668);
      store v_11659 (extract v_11669 1 65) 8;
      v_11672 <- eval (extract v_11668 57 65);
      v_11673 <- eval (eq v_11672 (expression.bv_nat 8 1));
      v_11674 <- eval (isBitSet v_11669 0);
      v_11680 <- eval (eq v_11672 (expression.bv_nat 8 0));
      v_11683 <- getRegister of;
      setRegister cf v_11674;
      setRegister of (bit_or (bit_and v_11673 (notBool_ (eq v_11674 (isBitSet v_11669 1)))) (bit_and (notBool_ v_11673) (bit_or (bit_and (notBool_ v_11680) undef) (bit_and v_11680 (eq v_11683 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
