def rclq1 : instruction :=
  definst "rclq" $ do
    pattern fun cl (v_2391 : reg (bv 64)) => do
      v_3986 <- getRegister cf;
      v_3989 <- getRegister v_2391;
      v_3991 <- getRegister rcx;
      v_3995 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_3991 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_3997 <- eval (rolHelper (concat (mux (eq v_3986 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_3989) (uvalueMInt v_3995) 0);
      v_3998 <- eval (extract v_3997 0 1);
      v_3999 <- eval (extract v_3995 57 65);
      v_4000 <- eval (eq v_3999 (expression.bv_nat 8 1));
      v_4008 <- eval (eq v_3999 (expression.bv_nat 8 0));
      v_4011 <- getRegister of;
      setRegister (lhs.of_reg v_2391) (extract v_3997 1 65);
      setRegister of (mux (bit_or (bit_and v_4000 (notBool_ (eq (eq v_3998 (expression.bv_nat 1 1)) (eq (extract v_3997 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4000) (bit_or (bit_and (notBool_ v_4008) undef) (bit_and v_4008 (eq v_4011 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_3998;
      pure ()
    pat_end;
    pattern fun (v_2392 : imm int) (v_2396 : reg (bv 64)) => do
      v_4022 <- getRegister cf;
      v_4025 <- getRegister v_2396;
      v_4030 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2392 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_4032 <- eval (rolHelper (concat (mux (eq v_4022 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4025) (uvalueMInt v_4030) 0);
      v_4033 <- eval (extract v_4032 0 1);
      v_4034 <- eval (extract v_4030 57 65);
      v_4035 <- eval (eq v_4034 (expression.bv_nat 8 1));
      v_4043 <- eval (eq v_4034 (expression.bv_nat 8 0));
      v_4046 <- getRegister of;
      setRegister (lhs.of_reg v_2396) (extract v_4032 1 65);
      setRegister of (mux (bit_or (bit_and v_4035 (notBool_ (eq (eq v_4033 (expression.bv_nat 1 1)) (eq (extract v_4032 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4035) (bit_or (bit_and (notBool_ v_4043) undef) (bit_and v_4043 (eq v_4046 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4033;
      pure ()
    pat_end;
    pattern fun $0x1 (v_2400 : reg (bv 64)) => do
      v_4057 <- getRegister cf;
      v_4060 <- getRegister v_2400;
      v_4061 <- eval (concat (mux (eq v_4057 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4060);
      v_4063 <- eval (bitwidthMInt v_4061);
      v_4069 <- eval (add (extract (shl v_4061 1) 0 v_4063) (concat (mi (sub v_4063 1) 0) (extract v_4061 0 1)));
      v_4070 <- eval (extract v_4069 0 1);
      setRegister (lhs.of_reg v_2400) (extract v_4069 1 65);
      setRegister of (mux (notBool_ (eq (eq v_4070 (expression.bv_nat 1 1)) (eq (extract v_4069 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4070;
      pure ()
    pat_end;
    pattern fun cl (v_2378 : Mem) => do
      v_13431 <- evaluateAddress v_2378;
      v_13432 <- getRegister cf;
      v_13435 <- load v_13431 8;
      v_13437 <- getRegister rcx;
      v_13441 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (extract v_13437 56 64) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_13443 <- eval (rolHelper (concat (mux (eq v_13432 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13435) (uvalueMInt v_13441) 0);
      store v_13431 (extract v_13443 1 65) 8;
      v_13446 <- eval (extract v_13443 0 1);
      v_13447 <- eval (extract v_13441 57 65);
      v_13448 <- eval (eq v_13447 (expression.bv_nat 8 1));
      v_13456 <- eval (eq v_13447 (expression.bv_nat 8 0));
      v_13459 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13448 (notBool_ (eq (eq v_13446 (expression.bv_nat 1 1)) (eq (extract v_13443 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13448) (bit_or (bit_and (notBool_ v_13456) undef) (bit_and v_13456 (eq v_13459 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_13446;
      pure ()
    pat_end;
    pattern fun (v_2381 : imm int) (v_2382 : Mem) => do
      v_13468 <- evaluateAddress v_2382;
      v_13469 <- getRegister cf;
      v_13472 <- load v_13468 8;
      v_13477 <- eval (urem (concat (expression.bv_nat 57 0) (bv_and (handleImmediateWithSignExtend v_2381 8 8) (expression.bv_nat 8 63))) (expression.bv_nat 65 65));
      v_13479 <- eval (rolHelper (concat (mux (eq v_13469 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13472) (uvalueMInt v_13477) 0);
      store v_13468 (extract v_13479 1 65) 8;
      v_13482 <- eval (extract v_13479 0 1);
      v_13483 <- eval (extract v_13477 57 65);
      v_13484 <- eval (eq v_13483 (expression.bv_nat 8 1));
      v_13492 <- eval (eq v_13483 (expression.bv_nat 8 0));
      v_13495 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13484 (notBool_ (eq (eq v_13482 (expression.bv_nat 1 1)) (eq (extract v_13479 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13484) (bit_or (bit_and (notBool_ v_13492) undef) (bit_and v_13492 (eq v_13495 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_13482;
      pure ()
    pat_end
