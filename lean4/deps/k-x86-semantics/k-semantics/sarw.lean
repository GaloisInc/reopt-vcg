def sarw1 : instruction :=
  definst "sarw" $ do
    pattern fun cl (v_3115 : reg (bv 16)) => do
      v_7929 <- getRegister rcx;
      v_7931 <- eval (bv_and (extract v_7929 56 64) (expression.bv_nat 8 31));
      v_7932 <- eval (eq v_7931 (expression.bv_nat 8 0));
      v_7933 <- eval (notBool_ v_7932);
      v_7934 <- getRegister v_3115;
      v_7935 <- eval (concat v_7934 (expression.bv_nat 1 0));
      v_7941 <- eval (ashr (mi (bitwidthMInt v_7935) (svalueMInt v_7935)) (uvalueMInt (concat (expression.bv_nat 9 0) v_7931)));
      v_7945 <- getRegister cf;
      v_7953 <- getRegister sf;
      v_7958 <- eval (bit_and v_7933 undef);
      v_7959 <- getRegister af;
      v_7964 <- eval (extract v_7941 0 16);
      v_7967 <- getRegister zf;
      v_8002 <- getRegister pf;
      v_8009 <- getRegister of;
      setRegister (lhs.of_reg v_3115) v_7964;
      setRegister of (mux (bit_and (notBool_ (eq v_7931 (expression.bv_nat 8 1))) (bit_or v_7958 (bit_and v_7932 (eq v_8009 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7933 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7941 15 16) (expression.bv_nat 1 1)) (eq (extract v_7941 14 15) (expression.bv_nat 1 1)))) (eq (extract v_7941 13 14) (expression.bv_nat 1 1)))) (eq (extract v_7941 12 13) (expression.bv_nat 1 1)))) (eq (extract v_7941 11 12) (expression.bv_nat 1 1)))) (eq (extract v_7941 10 11) (expression.bv_nat 1 1)))) (eq (extract v_7941 9 10) (expression.bv_nat 1 1)))) (eq (extract v_7941 8 9) (expression.bv_nat 1 1)))) (bit_and v_7932 (eq v_8002 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7933 (eq v_7964 (expression.bv_nat 16 0))) (bit_and v_7932 (eq v_7967 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7958 (bit_and v_7932 (eq v_7959 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7933 (eq (extract v_7941 0 1) (expression.bv_nat 1 1))) (bit_and v_7932 (eq v_7953 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7933 (eq (extract v_7941 16 17) (expression.bv_nat 1 1))) (bit_and v_7932 (eq v_7945 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3116 : imm int) (v_3120 : reg (bv 16)) => do
      v_8023 <- eval (bv_and (handleImmediateWithSignExtend v_3116 8 8) (expression.bv_nat 8 31));
      v_8024 <- eval (eq v_8023 (expression.bv_nat 8 0));
      v_8025 <- eval (notBool_ v_8024);
      v_8026 <- getRegister v_3120;
      v_8027 <- eval (concat v_8026 (expression.bv_nat 1 0));
      v_8033 <- eval (ashr (mi (bitwidthMInt v_8027) (svalueMInt v_8027)) (uvalueMInt (concat (expression.bv_nat 9 0) v_8023)));
      v_8037 <- getRegister cf;
      v_8045 <- getRegister sf;
      v_8050 <- eval (bit_and v_8025 undef);
      v_8051 <- getRegister af;
      v_8056 <- eval (extract v_8033 0 16);
      v_8059 <- getRegister zf;
      v_8094 <- getRegister pf;
      v_8101 <- getRegister of;
      setRegister (lhs.of_reg v_3120) v_8056;
      setRegister of (mux (bit_and (notBool_ (eq v_8023 (expression.bv_nat 8 1))) (bit_or v_8050 (bit_and v_8024 (eq v_8101 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_8025 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_8033 15 16) (expression.bv_nat 1 1)) (eq (extract v_8033 14 15) (expression.bv_nat 1 1)))) (eq (extract v_8033 13 14) (expression.bv_nat 1 1)))) (eq (extract v_8033 12 13) (expression.bv_nat 1 1)))) (eq (extract v_8033 11 12) (expression.bv_nat 1 1)))) (eq (extract v_8033 10 11) (expression.bv_nat 1 1)))) (eq (extract v_8033 9 10) (expression.bv_nat 1 1)))) (eq (extract v_8033 8 9) (expression.bv_nat 1 1)))) (bit_and v_8024 (eq v_8094 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_8025 (eq v_8056 (expression.bv_nat 16 0))) (bit_and v_8024 (eq v_8059 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_8050 (bit_and v_8024 (eq v_8051 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_8025 (eq (extract v_8033 0 1) (expression.bv_nat 1 1))) (bit_and v_8024 (eq v_8045 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_8025 (eq (extract v_8033 16 17) (expression.bv_nat 1 1))) (bit_and v_8024 (eq v_8037 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_3127 : reg (bv 16)) => do
      v_8116 <- getRegister v_3127;
      v_8117 <- eval (concat v_8116 (expression.bv_nat 1 0));
      v_8121 <- eval (ashr (mi (bitwidthMInt v_8117) (svalueMInt v_8117)) 1);
      v_8124 <- eval (extract v_8121 0 16);
      setRegister (lhs.of_reg v_3127) v_8124;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_8121 8 16));
      setRegister zf (zeroFlag v_8124);
      setRegister af undef;
      setRegister sf (extract v_8121 0 1);
      setRegister cf (extract v_8121 16 17);
      pure ()
    pat_end;
    pattern fun (v_3123 : reg (bv 16)) => do
      v_9997 <- getRegister v_3123;
      v_9998 <- eval (concat v_9997 (expression.bv_nat 1 0));
      v_10002 <- eval (ashr (mi (bitwidthMInt v_9998) (svalueMInt v_9998)) 1);
      v_10009 <- eval (extract v_10002 0 16);
      setRegister (lhs.of_reg v_3123) v_10009;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_10002 8 16));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_10009);
      setRegister sf (mux (eq (extract v_10002 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_10002 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3123 : reg (bv 16)) => do
      v_10020 <- getRegister v_3123;
      v_10021 <- eval (concat v_10020 (expression.bv_nat 1 0));
      v_10025 <- eval (ashr (mi (bitwidthMInt v_10021) (svalueMInt v_10021)) 1);
      v_10028 <- eval (extract v_10025 0 16);
      setRegister (lhs.of_reg v_3123) v_10028;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_10025 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_10028);
      setRegister sf (extract v_10025 0 1);
      setRegister cf (extract v_10025 16 17);
      pure ()
    pat_end;
    pattern fun cl (v_3099 : Mem) => do
      v_17446 <- evaluateAddress v_3099;
      v_17447 <- load v_17446 2;
      v_17448 <- eval (concat v_17447 (expression.bv_nat 1 0));
      v_17452 <- getRegister rcx;
      v_17454 <- eval (bv_and (extract v_17452 56 64) (expression.bv_nat 8 31));
      v_17457 <- eval (ashr (mi (bitwidthMInt v_17448) (svalueMInt v_17448)) (uvalueMInt (concat (expression.bv_nat 9 0) v_17454)));
      v_17458 <- eval (extract v_17457 0 16);
      store v_17446 v_17458 2;
      v_17460 <- eval (eq v_17454 (expression.bv_nat 8 0));
      v_17461 <- eval (notBool_ v_17460);
      v_17465 <- getRegister cf;
      v_17473 <- getRegister sf;
      v_17480 <- getRegister zf;
      v_17485 <- eval (bit_and v_17461 undef);
      v_17486 <- getRegister af;
      v_17521 <- getRegister pf;
      v_17528 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_17454 (expression.bv_nat 8 1))) (bit_or v_17485 (bit_and v_17460 (eq v_17528 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_17461 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_17457 15 16) (expression.bv_nat 1 1)) (eq (extract v_17457 14 15) (expression.bv_nat 1 1)))) (eq (extract v_17457 13 14) (expression.bv_nat 1 1)))) (eq (extract v_17457 12 13) (expression.bv_nat 1 1)))) (eq (extract v_17457 11 12) (expression.bv_nat 1 1)))) (eq (extract v_17457 10 11) (expression.bv_nat 1 1)))) (eq (extract v_17457 9 10) (expression.bv_nat 1 1)))) (eq (extract v_17457 8 9) (expression.bv_nat 1 1)))) (bit_and v_17460 (eq v_17521 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_17485 (bit_and v_17460 (eq v_17486 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_17461 (eq v_17458 (expression.bv_nat 16 0))) (bit_and v_17460 (eq v_17480 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_17461 (eq (extract v_17457 0 1) (expression.bv_nat 1 1))) (bit_and v_17460 (eq v_17473 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_17461 (eq (extract v_17457 16 17) (expression.bv_nat 1 1))) (bit_and v_17460 (eq v_17465 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3102 : imm int) (v_3103 : Mem) => do
      v_17540 <- evaluateAddress v_3103;
      v_17541 <- load v_17540 2;
      v_17542 <- eval (concat v_17541 (expression.bv_nat 1 0));
      v_17547 <- eval (bv_and (handleImmediateWithSignExtend v_3102 8 8) (expression.bv_nat 8 31));
      v_17550 <- eval (ashr (mi (bitwidthMInt v_17542) (svalueMInt v_17542)) (uvalueMInt (concat (expression.bv_nat 9 0) v_17547)));
      v_17551 <- eval (extract v_17550 0 16);
      store v_17540 v_17551 2;
      v_17553 <- eval (eq v_17547 (expression.bv_nat 8 0));
      v_17554 <- eval (notBool_ v_17553);
      v_17558 <- getRegister cf;
      v_17566 <- getRegister sf;
      v_17573 <- getRegister zf;
      v_17578 <- eval (bit_and v_17554 undef);
      v_17579 <- getRegister af;
      v_17614 <- getRegister pf;
      v_17621 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_17547 (expression.bv_nat 8 1))) (bit_or v_17578 (bit_and v_17553 (eq v_17621 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_17554 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_17550 15 16) (expression.bv_nat 1 1)) (eq (extract v_17550 14 15) (expression.bv_nat 1 1)))) (eq (extract v_17550 13 14) (expression.bv_nat 1 1)))) (eq (extract v_17550 12 13) (expression.bv_nat 1 1)))) (eq (extract v_17550 11 12) (expression.bv_nat 1 1)))) (eq (extract v_17550 10 11) (expression.bv_nat 1 1)))) (eq (extract v_17550 9 10) (expression.bv_nat 1 1)))) (eq (extract v_17550 8 9) (expression.bv_nat 1 1)))) (bit_and v_17553 (eq v_17614 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_17578 (bit_and v_17553 (eq v_17579 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_17554 (eq v_17551 (expression.bv_nat 16 0))) (bit_and v_17553 (eq v_17573 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_17554 (eq (extract v_17550 0 1) (expression.bv_nat 1 1))) (bit_and v_17553 (eq v_17566 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_17554 (eq (extract v_17550 16 17) (expression.bv_nat 1 1))) (bit_and v_17553 (eq v_17558 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3108 : Mem) => do
      v_18526 <- evaluateAddress v_3108;
      v_18527 <- load v_18526 2;
      v_18528 <- eval (concat v_18527 (expression.bv_nat 1 0));
      v_18532 <- eval (ashr (mi (bitwidthMInt v_18528) (svalueMInt v_18528)) 1);
      v_18533 <- eval (extract v_18532 0 16);
      store v_18526 v_18533 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18532 8 16));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18533);
      setRegister sf (mux (eq (extract v_18532 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_18532 16 17) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3108 : Mem) => do
      v_18550 <- evaluateAddress v_3108;
      v_18551 <- load v_18550 2;
      v_18552 <- eval (concat v_18551 (expression.bv_nat 1 0));
      v_18556 <- eval (ashr (mi (bitwidthMInt v_18552) (svalueMInt v_18552)) 1);
      v_18557 <- eval (extract v_18556 0 16);
      store v_18550 v_18557 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18556 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_18557);
      setRegister sf (extract v_18556 0 1);
      setRegister cf (extract v_18556 16 17);
      pure ()
    pat_end
