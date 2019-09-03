def blsmskq1 : instruction :=
  definst "blsmskq" $ do
    pattern fun (v_2982 : reg (bv 64)) (v_2983 : reg (bv 64)) => do
      v_5951 <- getRegister v_2982;
      v_5954 <- eval (sub v_5951 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_2983) (bv_xor v_5954 v_5951);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (expression.bv_nat 1 0);
      setRegister af undef;
      setRegister sf (bv_xor (extract v_5954 0 1) (extract v_5951 0 1));
      setRegister cf (mux (eq v_5951 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2977 : Mem) (v_2978 : reg (bv 64)) => do
      v_9645 <- evaluateAddress v_2977;
      v_9646 <- load v_9645 8;
      v_9649 <- eval (sub v_9646 (expression.bv_nat 64 1));
      setRegister (lhs.of_reg v_2978) (bv_xor v_9649 v_9646);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (expression.bv_nat 1 0);
      setRegister af undef;
      setRegister sf (bv_xor (extract v_9649 0 1) (extract v_9646 0 1));
      setRegister cf (mux (eq v_9646 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
