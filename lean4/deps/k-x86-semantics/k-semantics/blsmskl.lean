def blsmskl1 : instruction :=
  definst "blsmskl" $ do
    pattern fun (v_2986 : reg (bv 32)) (v_2987 : reg (bv 32)) => do
      v_6087 <- getRegister v_2986;
      v_6090 <- eval (sub v_6087 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2987) (bv_xor v_6090 v_6087);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (expression.bv_nat 1 0);
      setRegister af undef;
      setRegister sf (bv_xor (extract v_6090 0 1) (extract v_6087 0 1));
      setRegister cf (mux (eq v_6087 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2981 : Mem) (v_2982 : reg (bv 32)) => do
      v_9917 <- evaluateAddress v_2981;
      v_9918 <- load v_9917 4;
      v_9921 <- eval (sub v_9918 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2982) (bv_xor v_9921 v_9918);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf undef;
      setRegister zf (expression.bv_nat 1 0);
      setRegister af undef;
      setRegister sf (bv_xor (extract v_9921 0 1) (extract v_9918 0 1));
      setRegister cf (mux (eq v_9918 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
