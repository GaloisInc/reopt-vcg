def blsmskq1 : instruction :=
  definst "blsmskq" $ do
    pattern fun (v_2995 : reg (bv 64)) (v_2996 : reg (bv 64)) => do
      v_6106 <- getRegister v_2995;
      v_6109 <- eval (sub v_6106 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_2996) (bv_xor v_6109 v_6106);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (expression.bv_nat 1 0);
      setRegister af undef;
      setRegister sf (bv_xor (extract v_6109 0 1) (extract v_6106 0 1));
      setRegister cf (mux (eq v_6106 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2990 : Mem) (v_2991 : reg (bv 64)) => do
      v_9933 <- evaluateAddress v_2990;
      v_9934 <- load v_9933 8;
      v_9937 <- eval (sub v_9934 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_2991) (bv_xor v_9937 v_9934);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (expression.bv_nat 1 0);
      setRegister af undef;
      setRegister sf (bv_xor (extract v_9937 0 1) (extract v_9934 0 1));
      setRegister cf (mux (eq v_9934 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
