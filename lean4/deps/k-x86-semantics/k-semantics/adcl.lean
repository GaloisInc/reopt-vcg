def adcl1 : instruction :=
  definst "adcl" $ do
    pattern fun (v_2448 : imm int) eax => do
      v_4036 <- getRegister cf;
      v_4038 <- eval (handleImmediateWithSignExtend v_2448 32 32);
      v_4039 <- eval (concat (expression.bv_nat 1 0) v_4038);
      v_4042 <- getRegister rax;
      v_4045 <- eval (add (mux (eq v_4036 (expression.bv_nat 1 1)) (add v_4039 (expression.bv_nat 33 1)) v_4039) (concat (expression.bv_nat 1 0) (extract v_4042 32 64)));
      v_4047 <- eval (extract v_4045 1 2);
      v_4053 <- eval (extract v_4045 1 33);
      v_4058 <- eval (eq (extract v_4038 0 1) (expression.bv_nat 1 1));
      setRegister eax v_4053;
      setRegister of (mux (bit_and (eq v_4058 (eq (extract v_4042 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_4058 (eq v_4047 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4045 25 33));
      setRegister zf (zeroFlag v_4053);
      setRegister af (bv_xor (bv_xor (extract v_4038 27 28) (extract v_4042 59 60)) (extract v_4045 28 29));
      setRegister sf v_4047;
      setRegister cf (extract v_4045 0 1);
      pure ()
    pat_end;
    pattern fun (v_2461 : imm int) (v_2460 : reg (bv 32)) => do
      v_4082 <- getRegister cf;
      v_4084 <- eval (handleImmediateWithSignExtend v_2461 32 32);
      v_4085 <- eval (concat (expression.bv_nat 1 0) v_4084);
      v_4088 <- getRegister v_2460;
      v_4090 <- eval (add (mux (eq v_4082 (expression.bv_nat 1 1)) (add v_4085 (expression.bv_nat 33 1)) v_4085) (concat (expression.bv_nat 1 0) v_4088));
      v_4092 <- eval (extract v_4090 1 2);
      v_4097 <- eval (extract v_4090 1 33);
      v_4102 <- eval (eq (extract v_4084 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2460) v_4097;
      setRegister of (mux (bit_and (eq v_4102 (eq (extract v_4088 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4102 (eq v_4092 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4090 25 33));
      setRegister zf (zeroFlag v_4097);
      setRegister af (bv_xor (extract (bv_xor v_4084 v_4088) 27 28) (extract v_4090 28 29));
      setRegister sf v_4092;
      setRegister cf (extract v_4090 0 1);
      pure ()
    pat_end;
    pattern fun (v_2469 : reg (bv 32)) (v_2470 : reg (bv 32)) => do
      v_4122 <- getRegister cf;
      v_4124 <- getRegister v_2469;
      v_4125 <- eval (concat (expression.bv_nat 1 0) v_4124);
      v_4128 <- getRegister v_2470;
      v_4130 <- eval (add (mux (eq v_4122 (expression.bv_nat 1 1)) (add v_4125 (expression.bv_nat 33 1)) v_4125) (concat (expression.bv_nat 1 0) v_4128));
      v_4132 <- eval (extract v_4130 1 2);
      v_4137 <- eval (extract v_4130 1 33);
      v_4142 <- eval (eq (extract v_4124 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2470) v_4137;
      setRegister of (mux (bit_and (eq v_4142 (eq (extract v_4128 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4142 (eq v_4132 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_4130 25 33));
      setRegister zf (zeroFlag v_4137);
      setRegister af (bv_xor (extract (bv_xor v_4124 v_4128) 27 28) (extract v_4130 28 29));
      setRegister sf v_4132;
      setRegister cf (extract v_4130 0 1);
      pure ()
    pat_end;
    pattern fun (v_2464 : Mem) (v_2465 : reg (bv 32)) => do
      v_9024 <- getRegister cf;
      v_9026 <- evaluateAddress v_2464;
      v_9027 <- load v_9026 4;
      v_9028 <- eval (concat (expression.bv_nat 1 0) v_9027);
      v_9031 <- getRegister v_2465;
      v_9033 <- eval (add (mux (eq v_9024 (expression.bv_nat 1 1)) (add v_9028 (expression.bv_nat 33 1)) v_9028) (concat (expression.bv_nat 1 0) v_9031));
      v_9035 <- eval (extract v_9033 1 2);
      v_9040 <- eval (extract v_9033 1 33);
      v_9045 <- eval (eq (extract v_9027 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2465) v_9040;
      setRegister of (mux (bit_and (eq v_9045 (eq (extract v_9031 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_9045 (eq v_9035 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_9033 25 33));
      setRegister zf (zeroFlag v_9040);
      setRegister af (bv_xor (extract (bv_xor v_9027 v_9031) 27 28) (extract v_9033 28 29));
      setRegister sf v_9035;
      setRegister cf (extract v_9033 0 1);
      pure ()
    pat_end;
    pattern fun (v_2452 : imm int) (v_2451 : Mem) => do
      v_10633 <- evaluateAddress v_2451;
      v_10634 <- getRegister cf;
      v_10636 <- eval (handleImmediateWithSignExtend v_2452 32 32);
      v_10637 <- eval (concat (expression.bv_nat 1 0) v_10636);
      v_10640 <- load v_10633 4;
      v_10642 <- eval (add (mux (eq v_10634 (expression.bv_nat 1 1)) (add v_10637 (expression.bv_nat 33 1)) v_10637) (concat (expression.bv_nat 1 0) v_10640));
      v_10643 <- eval (extract v_10642 1 33);
      store v_10633 v_10643 4;
      v_10646 <- eval (extract v_10642 1 2);
      v_10655 <- eval (eq (extract v_10636 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10655 (eq (extract v_10640 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10655 (eq v_10646 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10642 25 33));
      setRegister af (bv_xor (extract (bv_xor v_10636 v_10640) 27 28) (extract v_10642 28 29));
      setRegister zf (zeroFlag v_10643);
      setRegister sf v_10646;
      setRegister cf (extract v_10642 0 1);
      pure ()
    pat_end;
    pattern fun (v_2456 : reg (bv 32)) (v_2455 : Mem) => do
      v_10670 <- evaluateAddress v_2455;
      v_10671 <- getRegister cf;
      v_10673 <- getRegister v_2456;
      v_10674 <- eval (concat (expression.bv_nat 1 0) v_10673);
      v_10677 <- load v_10670 4;
      v_10679 <- eval (add (mux (eq v_10671 (expression.bv_nat 1 1)) (add v_10674 (expression.bv_nat 33 1)) v_10674) (concat (expression.bv_nat 1 0) v_10677));
      v_10680 <- eval (extract v_10679 1 33);
      store v_10670 v_10680 4;
      v_10683 <- eval (extract v_10679 1 2);
      v_10692 <- eval (eq (extract v_10673 0 1) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_10692 (eq (extract v_10677 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10692 (eq v_10683 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10679 25 33));
      setRegister af (bv_xor (extract (bv_xor v_10673 v_10677) 27 28) (extract v_10679 28 29));
      setRegister zf (zeroFlag v_10680);
      setRegister sf v_10683;
      setRegister cf (extract v_10679 0 1);
      pure ()
    pat_end
