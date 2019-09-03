def adcw1 : instruction :=
  definst "adcw" $ do
    pattern fun (v_2500 : imm int) ax => do
      v_4282 <- getRegister cf;
      v_4284 <- eval (handleImmediateWithSignExtend v_2500 16 16);
      v_4285 <- eval (concat (expression.bv_nat 1 0) v_4284);
      v_4288 <- getRegister rax;
      v_4291 <- eval (add (mux (eq v_4282 (expression.bv_nat 1 1)) (add v_4285 (expression.bv_nat 17 1)) v_4285) (concat (expression.bv_nat 1 0) (extract v_4288 48 64)));
      v_4293 <- eval (extract v_4291 1 2);
      v_4299 <- eval (extract v_4291 1 17);
      v_4304 <- eval (eq (extract v_4284 0 1) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_4288 0 48) v_4299);
      setRegister of (mux (bit_and (eq v_4304 (eq (extract v_4288 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_4304 (eq v_4293 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4291 9 17));
      setRegister zf (zeroFlag v_4299);
      setRegister af (bv_xor (bv_xor (extract v_4284 11 12) (extract v_4288 59 60)) (extract v_4291 12 13));
      setRegister sf v_4293;
      setRegister cf (extract v_4291 0 1);
      pure ()
    pat_end;
    pattern fun (v_2513 : imm int) (v_2512 : reg (bv 16)) => do
      v_4330 <- getRegister cf;
      v_4332 <- eval (handleImmediateWithSignExtend v_2513 16 16);
      v_4333 <- eval (concat (expression.bv_nat 1 0) v_4332);
      v_4336 <- getRegister v_2512;
      v_4338 <- eval (add (mux (eq v_4330 (expression.bv_nat 1 1)) (add v_4333 (expression.bv_nat 17 1)) v_4333) (concat (expression.bv_nat 1 0) v_4336));
      v_4340 <- eval (extract v_4338 1 2);
      v_4345 <- eval (extract v_4338 1 17);
      v_4350 <- eval (eq (extract v_4332 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2512) v_4345;
      setRegister of (mux (bit_and (eq v_4350 (eq (extract v_4336 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4350 (eq v_4340 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4338 9 17));
      setRegister zf (zeroFlag v_4345);
      setRegister af (bv_xor (extract (bv_xor v_4332 v_4336) 11 12) (extract v_4338 12 13));
      setRegister sf v_4340;
      setRegister cf (extract v_4338 0 1);
      pure ()
    pat_end;
    pattern fun (v_2521 : reg (bv 16)) (v_2522 : reg (bv 16)) => do
      v_4370 <- getRegister cf;
      v_4372 <- getRegister v_2521;
      v_4373 <- eval (concat (expression.bv_nat 1 0) v_4372);
      v_4376 <- getRegister v_2522;
      v_4378 <- eval (add (mux (eq v_4370 (expression.bv_nat 1 1)) (add v_4373 (expression.bv_nat 17 1)) v_4373) (concat (expression.bv_nat 1 0) v_4376));
      v_4380 <- eval (extract v_4378 1 2);
      v_4385 <- eval (extract v_4378 1 17);
      v_4390 <- eval (eq (extract v_4372 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2522) v_4385;
      setRegister of (mux (bit_and (eq v_4390 (eq (extract v_4376 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4390 (eq v_4380 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4378 9 17));
      setRegister zf (zeroFlag v_4385);
      setRegister af (bv_xor (extract (bv_xor v_4372 v_4376) 11 12) (extract v_4378 12 13));
      setRegister sf v_4380;
      setRegister cf (extract v_4378 0 1);
      pure ()
    pat_end;
    pattern fun (v_2516 : Mem) (v_2517 : reg (bv 16)) => do
      v_9102 <- getRegister cf;
      v_9104 <- evaluateAddress v_2516;
      v_9105 <- load v_9104 2;
      v_9106 <- eval (concat (expression.bv_nat 1 0) v_9105);
      v_9109 <- getRegister v_2517;
      v_9111 <- eval (add (mux (eq v_9102 (expression.bv_nat 1 1)) (add v_9106 (expression.bv_nat 17 1)) v_9106) (concat (expression.bv_nat 1 0) v_9109));
      v_9113 <- eval (extract v_9111 1 2);
      v_9114 <- eval (extract v_9111 1 17);
      v_9123 <- eval (eq (extract v_9105 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2517) v_9114;
      setRegister of (mux (bit_and (eq v_9123 (eq (extract v_9109 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9123 (eq v_9113 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9111 9 17));
      setRegister af (bv_xor (extract (bv_xor v_9105 v_9109) 11 12) (extract v_9111 12 13));
      setRegister zf (zeroFlag v_9114);
      setRegister sf v_9113;
      setRegister cf (extract v_9111 0 1);
      pure ()
    pat_end;
    pattern fun (v_2504 : imm int) (v_2503 : Mem) => do
      v_10783 <- evaluateAddress v_2503;
      v_10784 <- getRegister cf;
      v_10786 <- eval (handleImmediateWithSignExtend v_2504 16 16);
      v_10787 <- eval (concat (expression.bv_nat 1 0) v_10786);
      v_10790 <- load v_10783 2;
      v_10792 <- eval (add (mux (eq v_10784 (expression.bv_nat 1 1)) (add v_10787 (expression.bv_nat 17 1)) v_10787) (concat (expression.bv_nat 1 0) v_10790));
      v_10793 <- eval (extract v_10792 1 17);
      store v_10783 v_10793 2;
      v_10796 <- eval (extract v_10792 1 2);
      v_10805 <- eval (eq (extract v_10786 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10805 (eq (extract v_10790 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10805 (eq v_10796 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10792 9 17));
      setRegister af (bv_xor (extract (bv_xor v_10786 v_10790) 11 12) (extract v_10792 12 13));
      setRegister zf (zeroFlag v_10793);
      setRegister sf v_10796;
      setRegister cf (extract v_10792 0 1);
      pure ()
    pat_end;
    pattern fun (v_2508 : reg (bv 16)) (v_2507 : Mem) => do
      v_10820 <- evaluateAddress v_2507;
      v_10821 <- getRegister cf;
      v_10823 <- getRegister v_2508;
      v_10824 <- eval (concat (expression.bv_nat 1 0) v_10823);
      v_10827 <- load v_10820 2;
      v_10829 <- eval (add (mux (eq v_10821 (expression.bv_nat 1 1)) (add v_10824 (expression.bv_nat 17 1)) v_10824) (concat (expression.bv_nat 1 0) v_10827));
      v_10830 <- eval (extract v_10829 1 17);
      store v_10820 v_10830 2;
      v_10833 <- eval (extract v_10829 1 2);
      v_10842 <- eval (eq (extract v_10823 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10842 (eq (extract v_10827 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10842 (eq v_10833 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10829 9 17));
      setRegister af (bv_xor (extract (bv_xor v_10823 v_10827) 11 12) (extract v_10829 12 13));
      setRegister zf (zeroFlag v_10830);
      setRegister sf v_10833;
      setRegister cf (extract v_10829 0 1);
      pure ()
    pat_end
