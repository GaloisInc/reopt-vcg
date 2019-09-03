def blsrq1 : instruction :=
  definst "blsrq" $ do
    pattern fun (v_3000 : reg (bv 64)) (v_3001 : reg (bv 64)) => do
      v_5990 <- getRegister v_3000;
      v_5993 <- eval (sub v_5990 (expression.bv_nat 64 1));
      v_5997 <- eval (bv_and v_5993 v_5990);
      setRegister (lhs.of_reg v_3001) v_5997;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_5997);
      setRegister af undef;
      setRegister sf (bv_and (extract v_5993 0 1) (extract v_5990 0 1));
      setRegister cf (mux (eq v_5990 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2995 : Mem) (v_2996 : reg (bv 64)) => do
      v_9678 <- evaluateAddress v_2995;
      v_9679 <- load v_9678 8;
      v_9682 <- eval (sub v_9679 (expression.bv_nat 64 1));
      v_9686 <- eval (bv_and v_9682 v_9679);
      setRegister (lhs.of_reg v_2996) v_9686;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (zeroFlag v_9686);
      setRegister af undef;
      setRegister sf (bv_and (extract v_9682 0 1) (extract v_9679 0 1));
      setRegister cf (mux (eq v_9679 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
