def blsrq1 : instruction :=
  definst "blsrq" $ do
    pattern fun (v_3013 : reg (bv 64)) (v_3014 : reg (bv 64)) => do
      v_6145 <- getRegister v_3013;
      v_6148 <- eval (sub v_6145 (expression.bv_nat 64 1));
      v_6152 <- eval (bv_and v_6148 v_6145);
      setRegister (lhs.of_reg v_3014) v_6152;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_6152);
      setRegister af undef;
      setRegister sf (bv_and (extract v_6148 0 1) (extract v_6145 0 1));
      setRegister cf (mux (eq v_6145 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3008 : Mem) (v_3009 : reg (bv 64)) => do
      v_9966 <- evaluateAddress v_3008;
      v_9967 <- load v_9966 8;
      v_9970 <- eval (sub v_9967 (expression.bv_nat 64 1));
      v_9974 <- eval (bv_and v_9970 v_9967);
      setRegister (lhs.of_reg v_3009) v_9974;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_9974);
      setRegister sf (bv_and (extract v_9970 0 1) (extract v_9967 0 1));
      setRegister cf (mux (eq v_9967 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
