def adcl1 : instruction :=
  definst "adcl" $ do
    pattern fun (v_2434 : imm int) eax => do
      v_4023 <- getRegister cf;
      v_4025 <- eval (handleImmediateWithSignExtend v_2434 32 32);
      v_4026 <- eval (concat (expression.bv_nat 1 0) v_4025);
      v_4029 <- getRegister rax;
      v_4032 <- eval (add (mux (eq v_4023 (expression.bv_nat 1 1)) (add v_4026 (expression.bv_nat 33 1)) v_4026) (concat (expression.bv_nat 1 0) (extract v_4029 32 64)));
      v_4034 <- eval (extract v_4032 1 2);
      v_4040 <- eval (extract v_4032 1 33);
      v_4045 <- eval (eq (extract v_4025 0 1) (expression.bv_nat 1 1));
      setRegister eax v_4040;
      setRegister of (mux (bit_and (eq v_4045 (eq (extract v_4029 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_4045 (eq v_4034 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4032 25 33));
      setRegister zf (zeroFlag v_4040);
      setRegister af (bv_xor (bv_xor (extract v_4025 27 28) (extract v_4029 59 60)) (extract v_4032 28 29));
      setRegister sf v_4034;
      setRegister cf (extract v_4032 0 1);
      pure ()
    pat_end;
    pattern fun (v_2446 : imm int) (v_2448 : reg (bv 32)) => do
      v_4069 <- getRegister cf;
      v_4071 <- eval (handleImmediateWithSignExtend v_2446 32 32);
      v_4072 <- eval (concat (expression.bv_nat 1 0) v_4071);
      v_4075 <- getRegister v_2448;
      v_4077 <- eval (add (mux (eq v_4069 (expression.bv_nat 1 1)) (add v_4072 (expression.bv_nat 33 1)) v_4072) (concat (expression.bv_nat 1 0) v_4075));
      v_4079 <- eval (extract v_4077 1 2);
      v_4080 <- eval (extract v_4077 1 33);
      v_4089 <- eval (eq (extract v_4071 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2448) v_4080;
      setRegister of (mux (bit_and (eq v_4089 (eq (extract v_4075 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4089 (eq v_4079 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4077 25 33));
      setRegister af (bv_xor (extract (bv_xor v_4071 v_4075) 27 28) (extract v_4077 28 29));
      setRegister zf (zeroFlag v_4080);
      setRegister sf v_4079;
      setRegister cf (extract v_4077 0 1);
      pure ()
    pat_end;
    pattern fun (v_2456 : reg (bv 32)) (v_2457 : reg (bv 32)) => do
      v_4109 <- getRegister cf;
      v_4111 <- getRegister v_2456;
      v_4112 <- eval (concat (expression.bv_nat 1 0) v_4111);
      v_4115 <- getRegister v_2457;
      v_4117 <- eval (add (mux (eq v_4109 (expression.bv_nat 1 1)) (add v_4112 (expression.bv_nat 33 1)) v_4112) (concat (expression.bv_nat 1 0) v_4115));
      v_4119 <- eval (extract v_4117 1 2);
      v_4120 <- eval (extract v_4117 1 33);
      v_4129 <- eval (eq (extract v_4111 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2457) v_4120;
      setRegister of (mux (bit_and (eq v_4129 (eq (extract v_4115 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4129 (eq v_4119 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4117 25 33));
      setRegister af (bv_xor (extract (bv_xor v_4111 v_4115) 27 28) (extract v_4117 28 29));
      setRegister zf (zeroFlag v_4120);
      setRegister sf v_4119;
      setRegister cf (extract v_4117 0 1);
      pure ()
    pat_end;
    pattern fun (v_2451 : Mem) (v_2452 : reg (bv 32)) => do
      v_8884 <- getRegister cf;
      v_8886 <- evaluateAddress v_2451;
      v_8887 <- load v_8886 4;
      v_8888 <- eval (concat (expression.bv_nat 1 0) v_8887);
      v_8891 <- getRegister v_2452;
      v_8893 <- eval (add (mux (eq v_8884 (expression.bv_nat 1 1)) (add v_8888 (expression.bv_nat 33 1)) v_8888) (concat (expression.bv_nat 1 0) v_8891));
      v_8895 <- eval (extract v_8893 1 2);
      v_8896 <- eval (extract v_8893 1 33);
      v_8905 <- eval (eq (extract v_8887 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2452) v_8896;
      setRegister of (mux (bit_and (eq v_8905 (eq (extract v_8891 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8905 (eq v_8895 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8893 25 33));
      setRegister af (bv_xor (extract (bv_xor v_8887 v_8891) 27 28) (extract v_8893 28 29));
      setRegister zf (zeroFlag v_8896);
      setRegister sf v_8895;
      setRegister cf (extract v_8893 0 1);
      pure ()
    pat_end;
    pattern fun (v_2439 : imm int) (v_2438 : Mem) => do
      v_10347 <- evaluateAddress v_2438;
      v_10348 <- getRegister cf;
      v_10350 <- eval (handleImmediateWithSignExtend v_2439 32 32);
      v_10351 <- eval (concat (expression.bv_nat 1 0) v_10350);
      v_10354 <- load v_10347 4;
      v_10356 <- eval (add (mux (eq v_10348 (expression.bv_nat 1 1)) (add v_10351 (expression.bv_nat 33 1)) v_10351) (concat (expression.bv_nat 1 0) v_10354));
      v_10357 <- eval (extract v_10356 1 33);
      store v_10347 v_10357 4;
      v_10360 <- eval (extract v_10356 1 2);
      v_10369 <- eval (eq (extract v_10350 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10369 (eq (extract v_10354 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10369 (eq v_10360 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10356 25 33));
      setRegister af (bv_xor (extract (bv_xor v_10350 v_10354) 27 28) (extract v_10356 28 29));
      setRegister zf (zeroFlag v_10357);
      setRegister sf v_10360;
      setRegister cf (extract v_10356 0 1);
      pure ()
    pat_end;
    pattern fun (v_2443 : reg (bv 32)) (v_2442 : Mem) => do
      v_10384 <- evaluateAddress v_2442;
      v_10385 <- getRegister cf;
      v_10387 <- getRegister v_2443;
      v_10388 <- eval (concat (expression.bv_nat 1 0) v_10387);
      v_10391 <- load v_10384 4;
      v_10393 <- eval (add (mux (eq v_10385 (expression.bv_nat 1 1)) (add v_10388 (expression.bv_nat 33 1)) v_10388) (concat (expression.bv_nat 1 0) v_10391));
      v_10394 <- eval (extract v_10393 1 33);
      store v_10384 v_10394 4;
      v_10397 <- eval (extract v_10393 1 2);
      v_10406 <- eval (eq (extract v_10387 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10406 (eq (extract v_10391 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10406 (eq v_10397 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10393 25 33));
      setRegister af (bv_xor (extract (bv_xor v_10387 v_10391) 27 28) (extract v_10393 28 29));
      setRegister zf (zeroFlag v_10394);
      setRegister sf v_10397;
      setRegister cf (extract v_10393 0 1);
      pure ()
    pat_end
