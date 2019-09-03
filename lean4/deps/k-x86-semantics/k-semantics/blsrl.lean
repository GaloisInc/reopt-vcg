def blsrl1 : instruction :=
  definst "blsrl" $ do
    pattern fun (v_2991 : reg (bv 32)) (v_2992 : reg (bv 32)) => do
      v_5970 <- getRegister v_2991;
      v_5973 <- eval (sub v_5970 (expression.bv_nat 32 1));
      v_5977 <- eval (bv_and v_5973 v_5970);
      setRegister (lhs.of_reg v_2992) v_5977;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister af undef;
      setRegister zf (zeroFlag v_5977);
      setRegister sf (bv_and (extract v_5973 0 1) (extract v_5970 0 1));
      setRegister cf (mux (eq v_5970 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2986 : Mem) (v_2987 : reg (bv 32)) => do
      v_9661 <- evaluateAddress v_2986;
      v_9662 <- load v_9661 4;
      v_9665 <- eval (sub v_9662 (expression.bv_nat 32 1));
      v_9669 <- eval (bv_and v_9665 v_9662);
      setRegister (lhs.of_reg v_2987) v_9669;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9669);
      setRegister af undef;
      setRegister sf (bv_and (extract v_9665 0 1) (extract v_9662 0 1));
      setRegister cf (mux (eq v_9662 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
