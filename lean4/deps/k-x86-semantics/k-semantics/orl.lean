def orl1 : instruction :=
  definst "orl" $ do
    pattern fun (v_2960 : imm int) eax => do
      v_4794 <- getRegister rax;
      v_4796 <- eval (handleImmediateWithSignExtend v_2960 32 32);
      v_4800 <- eval (bv_or (extract v_4794 32 64) v_4796);
      setRegister eax v_4800;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4794 63 64) (extract v_4796 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4794 62 63) (extract v_4796 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4794 61 62) (extract v_4796 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4794 60 61) (extract v_4796 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4794 59 60) (extract v_4796 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4794 58 59) (extract v_4796 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4794 57 58) (extract v_4796 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4794 56 57) (extract v_4796 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4800);
      setRegister af undef;
      setRegister sf (bv_or (extract v_4794 32 33) (extract v_4796 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2972 : imm int) (v_2973 : reg (bv 32)) => do
      v_4863 <- getRegister v_2973;
      v_4865 <- eval (bv_or v_4863 (handleImmediateWithSignExtend v_2972 32 32));
      setRegister (lhs.of_reg v_2973) v_4865;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4865 24 32));
      setRegister zf (zeroFlag v_4865);
      setRegister af undef;
      setRegister sf (extract v_4865 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2981 : reg (bv 32)) (v_2982 : reg (bv 32)) => do
      v_4881 <- getRegister v_2982;
      v_4882 <- getRegister v_2981;
      v_4883 <- eval (bv_or v_4881 v_4882);
      setRegister (lhs.of_reg v_2982) v_4883;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4883 24 32));
      setRegister zf (zeroFlag v_4883);
      setRegister af undef;
      setRegister sf (extract v_4883 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2977 : Mem) (v_2978 : reg (bv 32)) => do
      v_9208 <- getRegister v_2978;
      v_9209 <- evaluateAddress v_2977;
      v_9210 <- load v_9209 4;
      v_9211 <- eval (bv_or v_9208 v_9210);
      setRegister (lhs.of_reg v_2978) v_9211;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9211 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_9211);
      setRegister sf (extract v_9211 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2965 : imm int) (v_2964 : Mem) => do
      v_11159 <- evaluateAddress v_2964;
      v_11160 <- load v_11159 4;
      v_11162 <- eval (bv_or v_11160 (handleImmediateWithSignExtend v_2965 32 32));
      store v_11159 v_11162 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11162 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_11162);
      setRegister sf (extract v_11162 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2969 : reg (bv 32)) (v_2968 : Mem) => do
      v_11174 <- evaluateAddress v_2968;
      v_11175 <- load v_11174 4;
      v_11176 <- getRegister v_2969;
      v_11177 <- eval (bv_or v_11175 v_11176);
      store v_11174 v_11177 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11177 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_11177);
      setRegister sf (extract v_11177 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
