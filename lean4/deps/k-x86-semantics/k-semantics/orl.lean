def orl1 : instruction :=
  definst "orl" $ do
    pattern fun (v_2948 : imm int) eax => do
      v_4705 <- getRegister rax;
      v_4707 <- eval (handleImmediateWithSignExtend v_2948 32 32);
      v_4711 <- eval (bv_or (extract v_4705 32 64) v_4707);
      setRegister eax v_4711;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4705 63 64) (extract v_4707 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4705 62 63) (extract v_4707 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4705 61 62) (extract v_4707 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4705 60 61) (extract v_4707 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4705 59 60) (extract v_4707 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4705 58 59) (extract v_4707 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4705 57 58) (extract v_4707 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4705 56 57) (extract v_4707 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4711);
      setRegister af undef;
      setRegister sf (bv_or (extract v_4705 32 33) (extract v_4707 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2960 : imm int) (v_2961 : reg (bv 32)) => do
      v_4774 <- getRegister v_2961;
      v_4776 <- eval (bv_or v_4774 (handleImmediateWithSignExtend v_2960 32 32));
      setRegister (lhs.of_reg v_2961) v_4776;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4776 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_4776);
      setRegister sf (extract v_4776 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2969 : reg (bv 32)) (v_2970 : reg (bv 32)) => do
      v_4792 <- getRegister v_2970;
      v_4793 <- getRegister v_2969;
      v_4794 <- eval (bv_or v_4792 v_4793);
      setRegister (lhs.of_reg v_2970) v_4794;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4794 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_4794);
      setRegister sf (extract v_4794 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2964 : Mem) (v_2965 : reg (bv 32)) => do
      v_9133 <- getRegister v_2965;
      v_9134 <- evaluateAddress v_2964;
      v_9135 <- load v_9134 4;
      v_9136 <- eval (bv_or v_9133 v_9135);
      setRegister (lhs.of_reg v_2965) v_9136;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9136 24 32));
      setRegister zf (zeroFlag v_9136);
      setRegister af undef;
      setRegister sf (extract v_9136 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2952 : imm int) (v_2951 : Mem) => do
      v_11207 <- evaluateAddress v_2951;
      v_11208 <- load v_11207 4;
      v_11210 <- eval (bv_or v_11208 (handleImmediateWithSignExtend v_2952 32 32));
      store v_11207 v_11210 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11210 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_11210);
      setRegister sf (extract v_11210 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2956 : reg (bv 32)) (v_2955 : Mem) => do
      v_11222 <- evaluateAddress v_2955;
      v_11223 <- load v_11222 4;
      v_11224 <- getRegister v_2956;
      v_11225 <- eval (bv_or v_11223 v_11224);
      store v_11222 v_11225 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11225 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_11225);
      setRegister sf (extract v_11225 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end
